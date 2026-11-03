/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Checks

/-!
# The D₄ divisor comparison

From the kernel-checked certificates of `DeligneDivisorD4Checks` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`d4_pairComparison : PairComparisonG D4sector`**;
* **`d4_divisorComparison : DivisorComparisonG D4sector`** (B8 at `(Δ)` for D₄);
* **`D4_sectorFusionBound_of_U5`**: `SectorFusionBound D4data F` from U5 alone;
* **`d4_carrierDim_le_demazureSum_of_U5_U6`**: the D₄ carrier bound from U5 and U6.
-/

namespace VOA.DeligneAudit.DeligneDivisor.D4

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneCarrier.D4 (D4data)
open VOA.DeligneAudit.DeligneCharacter (demazureSumCoeff d4DemazureHilb)

noncomputable section

theorem hn4 : D4sector.n = 28 := rfl

theorem hf4 : ∀ x c e, D4sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-! ## Unpacking the checks -/

theorem nodeChecks_sound {lo hi : ℕ} (h : nodeChecks lo hi = true) {i : ℕ} (h1 : lo ≤ i)
    (h2 : i < hi) : nodeCheck br 28 tab par i = true := by
  simp only [nodeChecks, List.all_eq_true, List.mem_range'] at h
  exact h i ⟨i - lo, by omega, by omega⟩

theorem d4_node (i : ℕ) (h0 : 0 < i) (h1 : i < 784) : nodeCheck br 28 tab par i = true := by
  rcases Nat.lt_or_ge i 100 with h | h
  · exact nodeChecks_sound d4_nodes_1 (by omega) h
  rcases Nat.lt_or_ge i 200 with h' | h'
  · exact nodeChecks_sound d4_nodes_100 h h'
  rcases Nat.lt_or_ge i 300 with h'' | h''
  · exact nodeChecks_sound d4_nodes_200 h' h''
  rcases Nat.lt_or_ge i 400 with h3 | h3
  · exact nodeChecks_sound d4_nodes_300 h'' h3
  rcases Nat.lt_or_ge i 500 with h4 | h4
  · exact nodeChecks_sound d4_nodes_400 h3 h4
  rcases Nat.lt_or_ge i 600 with h5 | h5
  · exact nodeChecks_sound d4_nodes_500 h4 h5
  rcases Nat.lt_or_ge i 700 with h6 | h6
  · exact nodeChecks_sound d4_nodes_600 h5 h6
  · exact nodeChecks_sound d4_nodes_700 h6 h1

theorem d4_tree (i : ℕ) (hi : i < 784) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := D4sector) (tab i)) := by
  refine levOK_tree hn4 hf4 ?_ ?_ 784 d4_node i hi
  · rw [d4_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin D4sector.n, x = D4sector.c₀ ↔ (x : ℕ) = 27 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (27 = u ∧ 27 = v) ↔ (u = 27 ∧ v = 27) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [d4_root.2]; exact ⟨rfl, rfl⟩

theorem d4_dep (i : ℕ) (hi : i < 784) : (par i).2.2.2.1 ≤ 4 := by
  have h := d4_depth
  simp only [depthCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := D4sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (d4_tree p.1 h1) (d4_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 28) : castQZ (S := D4sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 28) : castQZ (S := D4sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := D4sector) (L.flatMap F) = (L.map fun x => castQZ (S := D4sector) (F x)).sum := by
  induction L with
  | nil => exact castQZ_nil
  | cons x L ih => rw [List.flatMap_cons, castQZ_append, ih, List.map_cons, List.sum_cons]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ((List.range N).map g).sum = ∑ k ∈ Finset.range N, g k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_option_idx {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ r : Option (Fin 105), g (idx r) = ((List.range 106).map g).sum := by
  rw [Fintype.sum_option, list_sum_range, Finset.sum_range_succ, add_comm]
  congr 1

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 105)) (c d : Fin 28) : ℤ := qget (relZ (idx r)) c d

/-- The complement tables. -/
def U4 (r : Option (Fin 105)) : ZTab D4sector := castQZ (Uq (idx r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 28 ∧ t.2.1 < 28) (c d : Fin 28) :
    VOA.DeligneAudit.A2.entryMatrix (castL 28 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 28 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 28 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 28 t.1, Fin.ofNat 28 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hq4 (r : Option (Fin 105)) (c d : Fin 28) : D4sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show D4data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq]
  exact entryMatrix_castL_apply _ (relZ_range (idx_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem antiChecks_sound {lo hi : ℕ} (h : antiChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 28) (hcd : c < d) : antiCheck c d = true := by
  simp only [antiChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem symChecks_sound {lo hi : ℕ} (h : symChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 28) (hcd : c ≤ d) : symCheck c d = true := by
  simp only [symChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem d4_antiCheck (c d : ℕ) (_hc : c < 28) (hd : d < 28) (hcd : c < d) : antiCheck c d = true := by
  have hs : ∀ lo, antiChecks lo (lo + 4) = true → lo ≤ c → c < lo + 4 → antiCheck c d = true :=
    fun lo h h1 h2 => antiChecks_sound h h1 h2 hd hcd
  rcases Nat.lt_or_ge c 4 with h | h; · exact hs 0 d4_anti_0 (by omega) h
  rcases Nat.lt_or_ge c 8 with h' | h'; · exact hs 4 d4_anti_4 h h'
  rcases Nat.lt_or_ge c 12 with h3 | h3; · exact hs 8 d4_anti_8 h' h3
  rcases Nat.lt_or_ge c 16 with h4 | h4; · exact hs 12 d4_anti_12 h3 h4
  rcases Nat.lt_or_ge c 20 with h5 | h5; · exact hs 16 d4_anti_16 h4 h5
  rcases Nat.lt_or_ge c 24 with h6 | h6; · exact hs 20 d4_anti_20 h5 h6
  exact hs 24 d4_anti_24 h6 (by omega)

theorem d4_symCheck (c d : ℕ) (hc : c < 28) (hd : d < 28) (hcd : c ≤ d) : symCheck c d = true := by
  have hs : ∀ lo, symChecks lo (lo + 2) = true → lo ≤ c → c < lo + 2 → symCheck c d = true :=
    fun lo h h1 h2 => symChecks_sound h h1 h2 hd hcd
  have hc2 : c / 2 * 2 ≤ c ∧ c < c / 2 * 2 + 2 := ⟨Nat.div_mul_le_self c 2, by omega⟩
  have key : ∀ k, k < 14 → c / 2 = k → symCheck c d = true := by
    intro k hk hck
    subst hck
    interval_cases (c / 2)
    · exact hs 0 d4_sym_0 hc2.1 hc2.2
    · exact hs 2 d4_sym_2 hc2.1 hc2.2
    · exact hs 4 d4_sym_4 hc2.1 hc2.2
    · exact hs 6 d4_sym_6 hc2.1 hc2.2
    · exact hs 8 d4_sym_8 hc2.1 hc2.2
    · exact hs 10 d4_sym_10 hc2.1 hc2.2
    · exact hs 12 d4_sym_12 hc2.1 hc2.2
    · exact hs 14 d4_sym_14 hc2.1 hc2.2
    · exact hs 16 d4_sym_16 hc2.1 hc2.2
    · exact hs 18 d4_sym_18 hc2.1 hc2.2
    · exact hs 20 d4_sym_20 hc2.1 hc2.2
    · exact hs 22 d4_sym_22 hc2.1 hc2.2
    · exact hs 24 d4_sym_24 hc2.1 hc2.2
    · exact hs 26 d4_sym_26 hc2.1 hc2.2
  exact key (c / 2) (by omega) rfl

theorem d4_UCheck (k : ℕ) (hk : k < 106) : UCheck k = true := by
  have hs : ∀ lo, (List.range' lo 53).all UCheck = true → lo ≤ k → k < lo + 53 →
      UCheck k = true := by
    intro lo h h1 h2
    simp only [List.all_eq_true, List.mem_range'] at h
    exact h k ⟨k - lo, by omega, by omega⟩
  rcases Nat.lt_or_ge k 53 with h | h
  · exact hs 0 d4_U_0 (by omega) h
  · exact hs 53 d4_U_53 h (by omega)

theorem hA4 (c d : Fin 28) (hcd : c < d) : LevOK 4 1 (((8 : ℕ) : ℤ) • antiZ (S := D4sector) c d) := by
  have h := d4_antiCheck c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_checkB (S := D4sector) hn4 h.2
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((8 : ℕ) : ℤ)) = 8 from rfl, heq]
  exact levOK_comb _ h.1

theorem hU4 (r : Option (Fin 105)) : LevOK 4 2 (U4 r) := by
  have h := d4_UCheck (idx r) (idx_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_checkB (S := D4sector) hn4 h.2
  rw [U4, heq]
  exact levOK_comb _ h.1

theorem castQZ_psiList (c d : Fin 28) :
    castQZ (S := D4sector) (psiList c d) = -∑ r, (qI r c d + qI r d c) • U4 r := by
  rw [psiList, castQZ_flatMap, ← Finset.sum_neg_distrib]
  have this := sum_option_idx (M := ZTab D4sector)
    (fun k => -((psiZ k c d) • castQZ (S := D4sector) (Uq k)))
  rw [show (∑ r, -((qI r c d + qI r d c) • U4 r)) =
    ∑ r, -((psiZ (idx r) c d) • castQZ (S := D4sector) (Uq (idx r))) from rfl, this]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  split_ifs with h
  · rw [castQZ_nil, h, zero_smul, neg_zero]
  · rw [castQZ_smulQ, neg_smul]

theorem hV4 (c d : Fin 28) (hcd : c ≤ d) :
    LevOK 4 0 (((384 : ℕ) : ℤ) • symZ (S := D4sector) c d - ∑ r, (qI r c d + qI r d c) • U4 r) := by
  have h := d4_symCheck c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_checkB (S := D4sector) hn4 h.2
  rw [castQZ_append, castQZ_smulQ, castQZ_symQ, castQZ_psiList] at heq
  rw [show (((384 : ℕ) : ℤ)) = 384 from rfl, sub_eq_add_neg]
  have e : ∀ r, qI r c d + qI r d c = psiZ (idx r) c d := fun r => rfl
  rw [heq]
  exact levOK_comb _ h.1

/-! ## The D₄ divisor comparison -/

/-- **The D₄ pair comparison.** -/
theorem d4_pairComparison : PairComparisonG D4sector :=
  pairComparisonG_of_cert (S := D4sector) qI hq4 4 8 384 (by norm_num) (by norm_num) U4 hA4 hU4 hV4

/-- **The D₄ divisor comparison (B8 at `(Δ)`).** -/
theorem d4_divisorComparison : DivisorComparisonG D4sector :=
  divisorComparisonG_of_pair d4_pairComparison

/-- **The D₄ sector fusion bound from U5 alone.** -/
theorem D4_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG D4sector F) :
    SectorFusionBound D4data F :=
  D4_sectorFusionBound F hU5 d4_divisorComparison

/-- **D₄ carrier side from U5 and U6**: `Σ_p dim Carrier p N ≤ D_N`. -/
theorem d4_carrierDim_le_demazureSum_of_U5_U6 (F : ℕ → PowerSeries ℚ)
    (hU5 : FusionModuleBoundG D4sector F)
    (hU6 : MixedFusionRecursion F (hilbSeries d4DemazureHilb)) (N : ℕ) :
    carrierDim D4data N ≤ demazureSumCoeff d4DemazureHilb N :=
  d4_carrierDim_le_demazureSum_of_sector F hU5 d4_divisorComparison hU6 N

end

end VOA.DeligneAudit.DeligneDivisor.D4

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.D4
#print axioms d4_pairComparison
#print axioms d4_divisorComparison
#print axioms D4_sectorFusionBound_of_U5
#print axioms d4_carrierDim_le_demazureSum_of_U5_U6
end AxiomAudit
