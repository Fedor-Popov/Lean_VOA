/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Solution
import VOA.DeligneAudit.DeligneCharacterD4

/-!
# The computable Demazure characters are the algebraic ones (layer 7, part 4)

The `List`-based `demazureChar cartanD4 thetaD4 wordD4 m` (root coordinates, `q`-exponents) maps
under `toR` to `B_R^m(1)` in `R` (`e`-coordinates, `q = qq`).  Hence `levelOneDemazureHilb`
computes the coefficients of `C_m = q^{m²}B^m(1)` at `z = 1`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- Root coordinates to `e`-coordinates. -/
def rootToV (μ : List ℤ) : V := ∑ i : Fin 4, μ.getD i 0 • rootV i

/-- A term `z^μ q^e · c` in `R`. -/
def termR (t : Term) : R := mon (rootToV t.1.1) (qq ^ t.1.2 * (t.2 : Kq))

/-- A term list in `R`. -/
def toR (f : LPoly) : R := (f.map termR).sum

theorem toR_nil : toR [] = 0 := rfl
theorem toR_cons (t : Term) (f : LPoly) : toR (t :: f) = termR t + toR f := by
  simp [toR]
theorem toR_append (f g : LPoly) : toR (f ++ g) = toR f + toR g := by simp [toR]
theorem toR_flatMap (f : LPoly) (g : Term → LPoly) :
    toR (f.flatMap g) = (f.map fun t => toR (g t)).sum := by
  induction f with
  | nil => rfl
  | cons t f ih => rw [List.flatMap_cons, toR_append, ih, List.map_cons, List.sum_cons]

theorem termR_add (k : List ℤ × ℤ) (a b : ℤ) : termR (k, a + b) = termR (k, a) + termR (k, b) := by
  simp only [termR, Int.cast_add, mul_add]
  rw [mon, mon, mon, ← AddMonoidAlgebra.single_add]

theorem termR_zero (k : List ℤ × ℤ) : termR (k, 0) = 0 := by
  rw [termR, Int.cast_zero, mul_zero, mon]; exact Finsupp.single_zero _

theorem toR_addTerm (t : Term) (g : LPoly) : toR (addTerm t g) = termR t + toR g := by
  induction g with
  | nil => simp [addTerm, toR]
  | cons s rest ih =>
      unfold addTerm
      split_ifs with h
      · have ht : termR t = termR (s.1, t.2) := by rw [← h]
        rw [toR_cons, toR_cons, termR_add, h, ← ht]; abel
      · rw [toR_cons, ih, toR_cons]; abel

theorem toR_normalize (f : LPoly) : toR (normalize f) = toR f := by
  have hfold : toR (f.foldr addTerm []) = toR f := by
    induction f with
    | nil => rfl
    | cons t f ih => rw [List.foldr_cons, toR_addTerm, ih, toR_cons]
  rw [normalize, ← hfold]
  generalize f.foldr addTerm [] = g
  induction g with
  | nil => rfl
  | cons t g ih =>
      rw [List.filter_cons]
      split_ifs with h
      · rw [toR_cons, toR_cons, ih]
      · simp only [decide_eq_true_eq, not_not] at h
        rw [toR_cons, ih, show t = (t.1, 0) by ext <;> simp [h], termR_zero, zero_add]

theorem toR_map_range (n : ℕ) (g : ℕ → Term) :
    toR ((List.range n).map g) = ∑ k ∈ Finset.range n, termR (g k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, toR_append, ih, Finset.sum_range_succ]
      simp [toR]

theorem rootToV_four (a b c d : ℤ) :
    rootToV [a, b, c, d] = a • rootV 0 + b • rootV 1 + c • rootV 2 + d • rootV 3 := by
  simp [rootToV, Fin.sum_univ_four]

theorem pairCoroot_eq (a b c d : ℤ) (i : Fin 4) :
    pairCoroot cartanD4 i [a, b, c, d] = dotZ (rootToV [a, b, c, d]) (rootV i) := by
  fin_cases i <;>
    simp [pairCoroot, cartanD4, dotZ, rootToV_four, rootV, zv, Fin.sum_univ_four, Pi.single_apply,
      Fin.succ] <;> ring

theorem rootToV_shiftAt (a b c d x : ℤ) (i : Fin 4) :
    rootToV (shiftAt [a, b, c, d] i x) = rootToV [a, b, c, d] + x • rootV i := by
  fin_cases i <;> simp [shiftAt, rootToV_four, add_smul] <;> abel

theorem shiftAt_four (a b c d x : ℤ) (i : Fin 4) :
    ∃ a' b' c' d', shiftAt [a, b, c, d] i x = [a', b', c', d'] := by
  fin_cases i <;> simp [shiftAt]

theorem toR_demazureFinTerm (i : Fin 4) (a b c d e k : ℤ) :
    toR (demazureFinTerm cartanD4 i (([a, b, c, d], e), k)) =
      piR (rootV i) (termR (([a, b, c, d], e), k)) := by
  rw [termR, piR_mon, piStr, ← pairCoroot_eq, demazureFinTerm]
  simp only
  split_ifs
  · rw [toR_map_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [termR, rootToV_shiftAt, smul_mon, mul_one]
    congr 1
    simp [sub_eq_add_neg]
  · rw [toR_map_range, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [termR, rootToV_shiftAt, smul_mon, mul_one, Int.cast_neg, mul_neg, mon, mon]
    exact Finsupp.single_neg _ _

theorem Atheta_D4 : ((List.range thetaD4.length).map fun i => pairCoroot cartanD4 i thetaD4) =
    [0, 1, 0, 0] := by decide

theorem dotZ_theta_four (a b c d : ℤ) : dotZ (rootToV [a, b, c, d]) thetaV = b := by
  simp [dotZ, rootToV_four, rootV, thetaV, zv, Fin.sum_univ_four, Pi.single_apply, Fin.succ]

theorem rootToV_shiftTheta (a b c d x : ℤ) :
    rootToV (shiftTheta [a, b, c, d] thetaD4 x) = rootToV [a, b, c, d] + x • thetaV := by
  have : thetaV = rootToV thetaD4 := by decide
  rw [this]
  simp [shiftTheta, thetaD4, rootToV_four, add_smul, mul_smul, mul_comm]
  abel

theorem toR_demazureZeroTerm (a b c d e k : ℤ) :
    toR (demazureZeroTerm cartanD4 thetaD4 (([a, b, c, d], e), k)) =
      pi0R (termR (([a, b, c, d], e), k)) := by
  rw [termR, pi0R_mon, pi0Str, dotZ_theta_four, demazureZeroTerm, Atheta_D4]
  have hs : (List.zipWith (· * ·) [0, 1, 0, 0] [a, b, c, d]).sum = b := by simp
  simp only [hs]
  split_ifs
  · rw [toR_map_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [termR, rootToV_shiftTheta, smul_mon]
    congr 1
    rw [zpow_sub₀ qq_ne_zero, zpow_natCast, zpow_neg, zpow_natCast]
    field_simp
  · rw [toR_map_range, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [termR, rootToV_shiftTheta, smul_mon, Int.cast_neg, mul_neg, mon, mon,
      show rootToV [a, b, c, d] + -((j : ℤ) + 1) • thetaV =
        rootToV [a, b, c, d] - ((j : ℤ) + 1) • thetaV by rw [neg_smul, ← sub_eq_add_neg]]
    rw [show qq ^ (e + ((j : ℤ) + 1)) * (k : Kq) = qq ^ e * k * qq ^ ((j : ℤ) + 1) by
      rw [zpow_add₀ qq_ne_zero]; ring]
    exact Finsupp.single_neg _ _

/-- All keys have four root coordinates. -/
def Good (f : LPoly) : Prop := ∀ t ∈ f, ∃ a b c d : ℤ, t.1.1 = [a, b, c, d]

theorem Good_normalize (f : LPoly) (hf : Good f) : Good (normalize f) := by
  have hfold : ∀ g : LPoly, Good g → Good (g.foldr addTerm []) := by
    intro g hg
    induction g with
    | nil => intro t ht; simp at ht
    | cons t g ih =>
        rw [List.foldr_cons]
        have hg' : Good g := fun s hs => hg s (List.mem_cons_of_mem _ hs)
        have ht : ∃ a b c d : ℤ, t.1.1 = [a, b, c, d] := hg t List.mem_cons_self
        generalize g.foldr addTerm [] = h at ih
        have ih' := ih hg'
        clear ih
        induction h with
        | nil => intro s hs; simp [addTerm] at hs; subst hs; exact ht
        | cons u h ih2 =>
            unfold addTerm
            split_ifs with heq
            · intro s hs
              rcases List.mem_cons.mp hs with hsu | hs
              · rw [hsu]; exact ht
              · exact ih' s (List.mem_cons_of_mem _ hs)
            · intro s hs
              rcases List.mem_cons.mp hs with hsu | hs
              · rw [hsu]; exact ih' u List.mem_cons_self
              · exact ih2 (fun w hw => ih' w (List.mem_cons_of_mem _ hw)) s hs
  intro t ht
  exact hfold f hf t (List.mem_of_mem_filter ht)

theorem toR_demazureFin (i : Fin 4) (f : LPoly) (hf : Good f) :
    toR (demazureFin cartanD4 i f) = piR (rootV i) (toR f) := by
  rw [demazureFin, toR_normalize, toR_flatMap, toR, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨a, b, c, d, h⟩ := hf t ht
  obtain ⟨⟨μ, e⟩, k⟩ := t
  simp only at h
  subst h
  exact toR_demazureFinTerm i a b c d e k

theorem toR_demazureZero (f : LPoly) (hf : Good f) :
    toR (demazureZero cartanD4 thetaD4 f) = pi0R (toR f) := by
  rw [demazureZero, toR_normalize, toR_flatMap, toR, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨a, b, c, d, h⟩ := hf t ht
  obtain ⟨⟨μ, e⟩, k⟩ := t
  simp only at h
  subst h
  exact toR_demazureZeroTerm a b c d e k

theorem Good_flatMap_fin (i : Fin 4) (f : LPoly) (hf : Good f) :
    Good (f.flatMap (demazureFinTerm cartanD4 i)) := by
  intro t ht
  obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨a, b, c, d, h⟩ := hf u hu
  obtain ⟨⟨μ, e⟩, k⟩ := u
  simp only at h
  subst h
  unfold demazureFinTerm at ht
  simp only at ht
  split_ifs at ht
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    exact shiftAt_four a b c d _ i
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    exact shiftAt_four a b c d _ i

theorem Good_flatMap_zero (f : LPoly) (hf : Good f) :
    Good (f.flatMap (demazureZeroTerm cartanD4 thetaD4)) := by
  intro t ht
  obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨a, b, c, d, h⟩ := hf u hu
  obtain ⟨⟨μ, e⟩, k⟩ := u
  simp only at h
  subst h
  unfold demazureZeroTerm at ht
  simp only at ht
  split_ifs at ht
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, _, rfl⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, _, rfl⟩

theorem Good_demazureFin (i : Fin 4) (f : LPoly) (hf : Good f) : Good (demazureFin cartanD4 i f) :=
  Good_normalize _ (Good_flatMap_fin i f hf)

theorem Good_demazureZero (f : LPoly) (hf : Good f) : Good (demazureZero cartanD4 thetaD4 f) :=
  Good_normalize _ (Good_flatMap_zero f hf)

theorem foldr_word (w : List (Fin 4)) (g : LPoly) (hg : Good g) :
    Good (w.foldr (fun (i : Fin 4) h => demazureFin cartanD4 (i : ℕ) h) g) ∧
      toR (w.foldr (fun (i : Fin 4) h => demazureFin cartanD4 (i : ℕ) h) g) =
        w.reverse.foldl (fun h i => piR (rootV i) h) (toR g) := by
  induction w with
  | nil => exact ⟨hg, rfl⟩
  | cons i w ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨Good_demazureFin i _ h1, ?_⟩
      rw [List.foldr_cons, toR_demazureFin i _ h1, h2, List.reverse_cons, List.foldl_append]
      rfl

theorem wordD4_eq : wordD4 = wordS.map (fun i : Fin 4 => (i : ℕ)) := by decide

theorem wordS_reverse : wordS.reverse = wordS := by decide

theorem demazureStep_D4 (f : LPoly) (hf : Good f) :
    Good (demazureStep cartanD4 thetaD4 wordD4 f) ∧
      toR (demazureStep cartanD4 thetaD4 wordD4 f) = BR (toR f) := by
  have h0 := Good_demazureZero f hf
  have := foldr_word wordS (demazureZero cartanD4 thetaD4 f) h0
  rw [demazureStep, wordD4_eq, List.foldr_map]
  refine ⟨this.1, ?_⟩
  rw [this.2, wordS_reverse, toR_demazureZero f hf]
  rfl

/-- **The computable Demazure characters are `B_R^m(1)`.** -/
theorem toR_demazureChar (m : ℕ) :
    Good (demazureChar cartanD4 thetaD4 wordD4 m) ∧
      toR (demazureChar cartanD4 thetaD4 wordD4 m) = BR^[m] 1 := by
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro t ht
        simp [demazureChar, thetaD4] at ht
        subst ht
        exact ⟨0, 0, 0, 0, rfl⟩
      · show toR [((List.replicate 4 0, 0), 1)] = 1
        rw [toR_cons, toR_nil, add_zero, termR, show List.replicate 4 (0 : ℤ) = [0, 0, 0, 0] from rfl,
          rootToV_four]
        simp only [zero_smul, add_zero, zpow_zero, Int.cast_one, mul_one]
        rfl
  | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      have := demazureStep_D4 _ h1
      rw [demazureChar, Function.iterate_succ_apply', ← demazureChar]
      exact ⟨this.1, by rw [this.2, h2, Function.iterate_succ_apply']⟩

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.toR_demazureChar
end AxiomAudit
