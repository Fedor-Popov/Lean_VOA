/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorChecks

/-!
# The F4 divisor comparison

From the kernel-checked certificates of `F4DivisorChecks` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`f4_pairComparison : PairComparisonG F4sector`**;
* **`f4_divisorComparison : DivisorComparisonG F4sector`** (B8 at `(Δ)` for F4);
* **`F4_sectorFusionBound_of_U5`**: `SectorFusionBound F4data F` from U5 alone.
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.F4 (F4data F4sector br relZ idx lab idx_lt idx_lab fullMatrix_eq relZ_range)

noncomputable section

theorem hnD : F4sector.n = 52 := rfl

theorem hfD : ∀ x c e, F4sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-! ## The tree -/

theorem f4_cols : ∀ x < 52, colCheck br colS 52 x = true := by
  have h := f4_colChecks
  simp only [colChecks, List.all_eq_true, List.mem_range] at h
  exact h

theorem f4_tree (i : ℕ) (hi : i < 2704) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := F4sector) (tab i)) := by
  refine levOK_treeC hnD hfD f4_cols ?_ ?_ 2704 f4_node i hi
  · rw [f4_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin F4sector.n, x = F4sector.c₀ ↔ (x : ℕ) = 45 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (45 = u ∧ 45 = v) ↔ (u = 45 ∧ v = 45) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [f4_root.2]; exact ⟨rfl, rfl⟩

theorem f4_dep (i : ℕ) (hi : i < 2704) : (par i).2.2.2.1 ≤ 4 := by
  have h := f4_depth
  simp only [depthCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := F4sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (f4_tree p.1 h1) (f4_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 52) : castQZ (S := F4sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 52) : castQZ (S := F4sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := F4sector) (L.flatMap F) = (L.map fun x => castQZ (S := F4sector) (F x)).sum := by
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
    ∑ r : Option (Fin 324), g (idx r) = ∑ k ∈ Finset.range 325, g k := by
  have h1 : ∑ r : Option (Fin 324), g (idx r) = g 324 + ∑ i : Fin 324, g i :=
    Fintype.sum_option _
  have h2 : ∑ i : Fin 324, g i = ∑ k ∈ Finset.range 324, g k := Fin.sum_univ_eq_sum_range g 324
  have h3 : ∑ k ∈ Finset.range 325, g k = ∑ k ∈ Finset.range 324, g k + g 324 :=
    Finset.sum_range_succ g 324
  rw [h1, h2, h3, add_comm]

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 324)) (c d : Fin 52) : ℤ := qget (relZ (idx r)) c d

/-- The complement tables. -/
def UD (r : Option (Fin 324)) : ZTab F4sector := castQZ (Uq (idx r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 52 ∧ t.2.1 < 52) (c d : Fin 52) :
    VOA.DeligneAudit.A2.entryMatrix (castL 52 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 52 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 52 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 52 t.1, Fin.ofNat 52 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hqD (r : Option (Fin 324)) (c d : Fin 52) :
    F4sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show F4data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq]
  exact entryMatrix_castL_apply _ (relZ_range (idx_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem hAD (c d : Fin 52) (hcd : c < d) : LevOK 4 1 (((48 : ℕ) : ℤ) • antiZ (S := F4sector) c d) := by
  have h := f4_antiCheck' c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := F4sector) (le_of_eq hnD) (encCheck_of_encLin h.2)
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((48 : ℕ) : ℤ)) = 48 from rfl, heq]
  exact levOK_comb _ h.1

theorem hUD (r : Option (Fin 324)) : LevOK 4 2 (UD r) := by
  have h := f4_UCheck (idx r) (idx_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := F4sector) (le_of_eq hnD) (encCheck_of_encLin h.2)
  rw [UD, heq]
  exact levOK_comb _ h.1

/-- Relations not listed under `{c, d}` do not contain the monomial. -/
theorem psiZ_eq_zero (c d : Fin 52) (hcd : c ≤ d) (k : ℕ) (hk : k < 325) (hnot : k ∉ psiT c d) :
    psiZ k c d = 0 := by
  have hc := f4_psiComplete
  simp only [psiComplete, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  have hz : ∀ a b : ℕ, (a = c ∧ b = d) ∨ (a = d ∧ b = c) → qget (relZ k) a b = 0 := by
    intro a b hab
    refine List.sum_eq_zero fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    split_ifs with h
    · exfalso
      apply hnot
      have := hc k hk t ht
      have hmm : min t.1 t.2.1 = c ∧ max t.1 t.2.1 = d := by
        have hcd' : (c : ℕ) ≤ d := hcd
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> obtain ⟨h1, h2⟩ := h <;> rw [h1, h2] <;>
          constructor <;> omega
      rwa [hmm.1, hmm.2] at this
    · rfl
  rw [psiZ, hz c d (Or.inl ⟨rfl, rfl⟩), hz d c (Or.inr ⟨rfl, rfl⟩), add_zero]

theorem castQZ_psi (c d : Fin 52) (hcd : c ≤ d) (hnd : (psiT c d).Nodup)
    (hlt : ∀ k ∈ psiT c d, k < 325) :
    castQZ (S := F4sector) (combQ tabX ((psiT c d).map fun k => (2704 + k, psiZ k c d))) =
      ∑ r, (qI r c d + qI r d c) • UD r := by
  rw [combQ, List.flatMap_map, castQZ_flatMap]
  rw [show (∑ r, (qI r c d + qI r d c) • UD r) =
    ∑ k ∈ Finset.range 325, (psiZ k c d) • castQZ (S := F4sector) (Uq k) from
      sum_option_idx (fun k => (psiZ k c d) • castQZ (S := F4sector) (Uq k))]
  have hsub : (psiT c d).toFinset ⊆ Finset.range 325 := by
    intro k hk; simpa using hlt k (List.mem_toFinset.mp hk)
  rw [← Finset.sum_subset hsub, List.sum_toFinset _ hnd]
  · congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [tabX, show ¬ (2704 + k < 2704) by omega, if_false, show 2704 + k - 2704 = k by omega,
      castQZ_smulQ]
  · intro k hk hnot
    rw [psiZ_eq_zero c d hcd k (by simpa using hk) (fun h => hnot (List.mem_toFinset.mpr h)),
      zero_smul]

theorem combQ_tabX (L : List (ℕ × ℤ)) (h : ∀ p ∈ L, p.1 < 2704) : combQ tabX L = combQ tab L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [combQ, List.flatMap_cons] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [tabX, h p List.mem_cons_self]

theorem hVD (c d : Fin 52) (hcd : c ≤ d) :
    LevOK 4 0 (((559104 : ℕ) : ℤ) • symZ (S := F4sector) c d - ∑ r, (qI r c d + qI r d c) • UD r) := by
  have h := f4_symCheck' c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlev, hnd⟩, hlt⟩, hz⟩ := h
  have heq := castQZ_eq_of_enc (S := F4sector) (le_of_eq hnD) (encCheck_of_encLin hz)
  have hlev' := hlev
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlev'
  rw [symCertX, combQ, List.flatMap_append, ← combQ, ← combQ, castQZ_append,
    combQ_tabX _ fun p hp => (hlev' p hp).1, castQZ_psi c d hcd (by simpa using hnd) hlt,
    castQZ_smulQ, castQZ_symQ] at heq
  rw [show (((559104 : ℕ) : ℤ)) = 559104 from rfl, heq, add_sub_cancel_right]
  exact levOK_comb _ hlev

/-! ## The F4 divisor comparison -/

/-- **The F4 pair comparison.** -/
theorem f4_pairComparison : PairComparisonG F4sector :=
  pairComparisonG_of_cert (S := F4sector) qI hqD 4 48 559104 (by norm_num) (by norm_num) UD hAD hUD hVD

/-- **The F4 divisor comparison (B8 at `(Δ)`).** -/
theorem f4_divisorComparison : DivisorComparisonG F4sector :=
  divisorComparisonG_of_pair f4_pairComparison

/-- **The F4 sector fusion bound from U5 alone.** -/
theorem F4_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG F4sector F) :
    SectorFusionBound F4data F :=
  sectorFusionBoundG F4sector F hU5 f4_divisorComparison

end

end VOA.DeligneAudit.DeligneDivisor.F4

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.F4
#print axioms f4_pairComparison
#print axioms f4_divisorComparison
#print axioms F4_sectorFusionBound_of_U5
end AxiomAudit
