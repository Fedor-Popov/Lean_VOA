/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointGramDegree

/-!
# Order-independent coloured affine contractions

Central contractions ignore the ordering of residual creation letters. Mapping
normal forms to multisets makes this precise and counts all matching positions,
including repetitions, without requiring the e/f swap to preserve PBW order.
-/
namespace VOA.AffineVOA.NormalOrdering
open Polynomial
/-- A current colour and its nonnegative creation depth. -/
abbrev Letter := Fin 3 × ℕ

/-- The creation colour paired with a given annihilator; depth is unchanged. -/
def oppositeLetter (a : Letter) : Letter := (Equiv.swap (0 : Fin 3) 1 a.1,a.2)

/-- Swapping the two charged colours twice restores the letter. -/
theorem oppositeLetter_involutive : Function.Involutive oppositeLetter := by
  intro a
  simp [oppositeLetter]

/-- The Killing pairing has only opposite-colour entries, with neutral
colour weight two and charged colour weight one. -/
theorem kappa_opposite (a b : Fin 3) :
    kappa a b = if Equiv.swap (0 : Fin 3) 1 a = b then (if a=2 then 2 else 1) else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [kappa, Equiv.swap_apply_def] <;> decide

/-- Positive depth times the nonzero Killing coefficient of a matching letter. -/
noncomputable def contractionWeight (a : Letter) : ℂ :=
  ((a.2 : ℂ)+1) * (if a.1=2 then 2 else 1)

/-- All allowed central matching coefficients are nonzero. -/
theorem contractionWeight_ne_zero (a : Letter) : contractionWeight a ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (show a.2+1 ≠ 0 by omega)
  · split_ifs <;> norm_num

/-- In natural indices a central contraction removes exactly an
opposite-colour letter of equal depth, with its explicit bracket weight. -/
theorem contractionNormal_cons_letter (a i : Letter) (w : List Letter) :
    contractionNormal a.1 ((a.2 : ℤ)+1) (i::w) =
      prepend i (contractionNormal a.1 ((a.2 : ℤ)+1) w) +
        if oppositeLetter a=i then Finsupp.single (1,w) (contractionWeight a) else 0 := by
  rw [contractionNormal]
  have hd : (a.2 : ℤ)+1-(i.2 : ℤ)-1=0 ↔ a.2=i.2 := by omega
  by_cases hi : oppositeLetter a=i
  · subst i
    simp [oppositeLetter, kappa_opposite, contractionWeight]
  · by_cases hh : a.2=i.2
    · have hc : Equiv.swap (0 : Fin 3) 1 a.1 ≠ i.1 := by
        intro hc
        exact hi (Prod.ext hc hh)
      simp [hh, kappa_opposite, hc, hi]
    · simp [hd, hh, hi]

/-- A normal-form label with an unordered residual creation multiset. -/
abbrev MultisetLabel := ℕ × Multiset Letter

/-- Finite coefficients on the central-power and creation-multiset labels. -/
abbrev MultisetForm := MultisetLabel →₀ ℂ

/-- Forget only the ordering of residual creation letters. -/
noncomputable def forgetOrder : NormalForm →ₗ[ℂ] MultisetForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (t.1,(t.2 : Multiset Letter)))

/-- Prefixing a creation letter becomes multiset insertion after forgetting order. -/
noncomputable def multisetPrepend (i : Letter) : MultisetForm →ₗ[ℂ] MultisetForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (t.1,i::ₘt.2))

/-- Central powers are unaffected by forgetting order. -/
noncomputable def multisetShift (p : ℕ) : MultisetForm →ₗ[ℂ] MultisetForm :=
  Finsupp.lmapDomain ℂ ℂ (fun t => (p+t.1,t.2))

/-- A single normal-form term maps to the corresponding unordered label. -/
theorem forgetOrder_single (t : Label) (c : ℂ) :
    forgetOrder (Finsupp.single t c) = Finsupp.single (t.1,(t.2 : Multiset Letter)) c := by
  simp [forgetOrder]

/-- Forgetting order commutes with prefixing. -/
theorem forgetOrder_prepend (i : Letter) (f : NormalForm) :
    forgetOrder (prepend i f) = multisetPrepend i (forgetOrder f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t c => simp [prepend, multisetPrepend, forgetOrder]

/-- Forgetting order commutes with adding central factors. -/
theorem forgetOrder_shift (p : ℕ) (f : NormalForm) :
    forgetOrder (centralShift p f) = multisetShift p (forgetOrder f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t c => simp [centralShift, multisetShift, forgetOrder]

/-- Every matching occurrence contributes the same residual multiset. The
coefficient is its exact multiplicity times the nonzero central weight. -/
theorem forgetOrder_contractionNormal (a : Letter) (w : List Letter) :
    forgetOrder (contractionNormal a.1 ((a.2 : ℤ)+1) w) =
      Finsupp.single (1,(w : Multiset Letter).erase (oppositeLetter a))
        (((w.count (oppositeLetter a) : ℕ) : ℂ) * contractionWeight a) := by
  induction w with
  | nil => simp [contractionNormal]
  | cons i w ih =>
    rw [contractionNormal_cons_letter, map_add, forgetOrder_prepend, ih]
    by_cases hi : oppositeLetter a=i
    · subst i
      simp only [ite_true, forgetOrder_single, multisetPrepend,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ← Multiset.cons_coe,
        Multiset.erase_cons_head, List.count_cons_self, Nat.cast_add, Nat.cast_one]
      by_cases ha : oppositeLetter a ∈ w
      · rw [Multiset.cons_erase (by simpa using ha), ← Finsupp.single_add]
        congr 1
        ring
      · have hc : w.count (oppositeLetter a)=0 := List.count_eq_zero.mpr ha
        simp [hc]
    · have hin : i ≠ oppositeLetter a := Ne.symm hi
      simp [hi, hin, multisetPrepend]

/-- Contraction on unordered labels counts matching letters and removes one. -/
noncomputable def multisetAct (a : Letter) : MultisetForm →ₗ[ℂ] MultisetForm :=
  Finsupp.linearCombination ℂ (fun t =>
    Finsupp.single (t.1+1,t.2.erase (oppositeLetter a))
      ((t.2.count (oppositeLetter a) : ℂ)*contractionWeight a))

/-- The unordered contraction is the exact image of the ordered algorithm. -/
theorem forgetOrder_actContraction (a : Letter) (f : NormalForm) :
    forgetOrder (actContraction a.1 ((a.2 : ℤ)+1) f) =
      multisetAct a (forgetOrder f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t c =>
    simp only [actContraction, Finsupp.linearCombination_single, map_smul,
      forgetOrder_shift, forgetOrder_contractionNormal, forgetOrder_single,
      multisetAct]
    simp [multisetShift]
    simp only [List.count_eq_countP, Bool.beq_eq_decide_eq]

/-- The vacuum coefficient keeps precisely the empty creation multiset. -/
noncomputable def multisetPolynomial : MultisetForm →ₗ[ℂ] Polynomial ℂ :=
  Finsupp.linearCombination ℂ (fun t => if t.2=0 then X^t.1 else 0)

/-- Forgetting creation order preserves the full central vacuum polynomial. -/
theorem centralPolynomial_forgetOrder (f : NormalForm) :
    centralPolynomial f = multisetPolynomial (forgetOrder f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single t c =>
    simp [centralPolynomial, multisetPolynomial, forgetOrder_single]

/-- Apply annihilators in list order, with the first letter acting first. -/
noncomputable def multisetRun : List Letter → MultisetForm →ₗ[ℂ] MultisetForm
  | [] => LinearMap.id
  | a::u => (multisetRun u).comp (multisetAct a)

/-- Reversed positive-mode words act by the unordered sequential algorithm. -/
theorem forgetOrder_applyContractions (u : List Letter) (f : NormalForm) :
    forgetOrder (applyContractions
      (u.reverse.map (fun a => (a.1,(a.2 : ℤ)+1))) f) =
      multisetRun u (forgetOrder f) := by
  have happ (v w : List (Fin 3 × ℤ)) :
      applyContractions (v++w) = (applyContractions v).comp (applyContractions w) := by
    induction v with
    | nil => rfl
    | cons a v ih => simp [applyContractions, ih, LinearMap.comp_assoc]
  induction u generalizing f with
  | nil => rfl
  | cons a u ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      happ, LinearMap.comp_apply, applyContractions, LinearMap.id_apply]
    rw [ih, forgetOrder_actContraction]
    rfl

/-- Exact central weight of a complete matching, including each repeated-letter
multiplicity. Grouping equal letters gives the usual factorial factors. -/
noncomputable def diagonalContraction : List Letter → ℂ
  | [] => 1
  | a::u => ((u.count a : ℂ)+1)*contractionWeight a*diagonalContraction u

/-- Every factor in a complete matching is a positive integer times one or two,
and in particular the product is nonzero. -/
theorem diagonalContraction_ne_zero (u : List Letter) : diagonalContraction u ≠ 0 := by
  induction u with
  | nil => exact one_ne_zero
  | cons a u ih =>
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (show u.count a+1 ≠ 0 by omega))
      (contractionWeight_ne_zero a)) ih

/-- A single unordered term contracts by its exact matching multiplicity. -/
theorem multisetAct_single (a : Letter) (p : ℕ) (s : Multiset Letter) (c : ℂ) :
    multisetAct a (Finsupp.single (p,s) c) =
      c • Finsupp.single (p+1,s.erase (oppositeLetter a))
        ((s.count (oppositeLetter a) : ℂ)*contractionWeight a) := by
  simp [multisetAct]

/-- Complete matching gives the exact nonzero diagonal product, regardless of
the order in which creation letters were originally written. -/
theorem multisetRun_diagonal (u : List Letter) (p : ℕ) :
    multisetRun u (Finsupp.single (p,(u : Multiset Letter).map oppositeLetter) 1) =
      Finsupp.single (p+u.length,0) (diagonalContraction u) := by
  induction u generalizing p with
  | nil => simp [multisetRun, diagonalContraction]
  | cons a u ih =>
    simp only [multisetRun, LinearMap.comp_apply, ← Multiset.cons_coe,
      Multiset.map_cons, multisetAct_single, one_smul, Multiset.erase_cons_head,
      Multiset.count_cons_self, Nat.cast_add, Nat.cast_one,
      Multiset.count_map_eq_count' oppositeLetter _ oppositeLetter_involutive.injective]
    rw [← Finsupp.smul_single_one, map_smul, ih]
    simp [diagonalContraction, Nat.add_assoc, Nat.add_comm]
    simp only [List.count_eq_countP, Bool.beq_eq_decide_eq]

/-- A nonzero vacuum contraction forces equality of the complete colour/depth
multisets. This support statement needs no ordering or equal-length assumption. -/
theorem multisetRun_vacuum_support (u : List Letter) (p : ℕ) (s : Multiset Letter)
    (hv : multisetPolynomial (multisetRun u (Finsupp.single (p,s) 1)) ≠ 0) :
    s = (u : Multiset Letter).map oppositeLetter := by
  induction u generalizing p s with
  | nil =>
    have hs : s=0 := by
      by_contra hs
      apply hv
      simp [multisetRun, multisetPolynomial, hs]
    simpa using hs
  | cons a u ih =>
    have hc : s.count (oppositeLetter a) ≠ 0 := by
      intro hz
      apply hv
      simp [multisetRun, multisetAct_single, hz]
    have ht : multisetPolynomial (multisetRun u
        (Finsupp.single (p+1,s.erase (oppositeLetter a)) 1)) ≠ 0 := by
      intro hz
      apply hv
      simp only [multisetRun, LinearMap.comp_apply, multisetAct_single, one_smul]
      rw [← Finsupp.smul_single_one, map_smul, map_smul, hz, smul_zero]
    have he := ih (p+1) (s.erase (oppositeLetter a)) ht
    rw [← Multiset.cons_coe, Multiset.map_cons, ← he]
    exact (Multiset.cons_erase (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc))).symm

/-- Different opposite-colour multisets have zero central vacuum polynomial. -/
theorem contractions_vacuum_zero (u v : List Letter)
    (h : (v : Multiset Letter) ≠ (u : Multiset Letter).map oppositeLetter) :
    centralPolynomial (applyContractions
      (u.reverse.map (fun a => (a.1,(a.2 : ℤ)+1))) (Finsupp.single (0,v) 1)) = 0 := by
  rw [centralPolynomial_forgetOrder, forgetOrder_applyContractions, forgetOrder_single]
  by_contra hn
  exact h (multisetRun_vacuum_support u 0 v hn)

/-- The complete matching polynomial has exactly the expected central power
and the explicit nonzero multiplicity product. -/
theorem contractions_vacuum_diagonal (u v : List Letter)
    (h : (v : Multiset Letter) = (u : Multiset Letter).map oppositeLetter) :
    centralPolynomial (applyContractions
      (u.reverse.map (fun a => (a.1,(a.2 : ℤ)+1))) (Finsupp.single (0,v) 1)) =
        diagonalContraction u • (X : Polynomial ℂ)^u.length := by
  rw [centralPolynomial_forgetOrder, forgetOrder_applyContractions, forgetOrder_single, h,
    multisetRun_diagonal]
  simp [multisetPolynomial]

end VOA.AffineVOA.NormalOrdering
