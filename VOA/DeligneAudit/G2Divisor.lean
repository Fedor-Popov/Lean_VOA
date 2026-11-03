/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2DivisorChecks

/-!
# The G2 divisor comparison

From the kernel-checked certificates of `G2DivisorChecks` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`g2_pairComparison : PairComparisonG G2sector`**;
* **`g2_divisorComparison : DivisorComparisonG G2sector`** (B8 at `(Δ)` for G2);
* **`G2_sectorFusionBound_of_U5`**: `SectorFusionBound G2data F` from U5 alone.
-/

namespace VOA.DeligneAudit.DeligneDivisor.G2

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneSector.G2 (G2data G2sector br relZ idx lab idx_lt idx_lab fullMatrix_eq relZ_range)

noncomputable section

theorem hnD : G2sector.n = 14 := rfl

theorem hfD : ∀ x c e, G2sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-! ## The tree -/

theorem g2_cols : ∀ x < 14, colCheck br colS 14 x = true := by
  have h := g2_colChecks
  simp only [colChecks, List.all_eq_true, List.mem_range] at h
  exact h

theorem g2_tree (i : ℕ) (hi : i < 196) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := G2sector) (tab i)) := by
  refine levOK_treeC hnD hfD g2_cols ?_ ?_ 196 g2_node i hi
  · rw [g2_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin G2sector.n, x = G2sector.c₀ ↔ (x : ℕ) = 12 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (12 = u ∧ 12 = v) ↔ (u = 12 ∧ v = 12) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [g2_root.2]; exact ⟨rfl, rfl⟩

theorem g2_dep (i : ℕ) (hi : i < 196) : (par i).2.2.2.1 ≤ 4 := by
  have h := g2_depth
  simp only [depthCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := G2sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (g2_tree p.1 h1) (g2_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 14) : castQZ (S := G2sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 14) : castQZ (S := G2sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := G2sector) (L.flatMap F) = (L.map fun x => castQZ (S := G2sector) (F x)).sum := by
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
    ∑ r : Option (Fin 27), g (idx r) = ∑ k ∈ Finset.range 28, g k := by
  have h1 : ∑ r : Option (Fin 27), g (idx r) = g 27 + ∑ i : Fin 27, g i :=
    Fintype.sum_option _
  have h2 : ∑ i : Fin 27, g i = ∑ k ∈ Finset.range 27, g k := Fin.sum_univ_eq_sum_range g 27
  have h3 : ∑ k ∈ Finset.range 28, g k = ∑ k ∈ Finset.range 27, g k + g 27 :=
    Finset.sum_range_succ g 27
  rw [h1, h2, h3, add_comm]

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 27)) (c d : Fin 14) : ℤ := qget (relZ (idx r)) c d

/-- The complement tables. -/
def UD (r : Option (Fin 27)) : ZTab G2sector := castQZ (Uq (idx r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 14 ∧ t.2.1 < 14) (c d : Fin 14) :
    VOA.DeligneAudit.A2.entryMatrix (castL 14 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 14 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 14 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 14 t.1, Fin.ofNat 14 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hqD (r : Option (Fin 27)) (c d : Fin 14) :
    G2sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show G2data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq]
  exact entryMatrix_castL_apply _ (relZ_range (idx_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem hAD (c d : Fin 14) (hcd : c < d) : LevOK 4 1 (((18 : ℕ) : ℤ) • antiZ (S := G2sector) c d) := by
  have h := g2_antiCheck' c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := G2sector) (le_of_eq hnD) (encCheck_of_encLin h.2)
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((18 : ℕ) : ℤ)) = 18 from rfl, heq]
  exact levOK_comb _ h.1

theorem hUD (r : Option (Fin 27)) : LevOK 4 2 (UD r) := by
  have h := g2_UCheck (idx r) (idx_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := G2sector) (le_of_eq hnD) (encCheck_of_encLin h.2)
  rw [UD, heq]
  exact levOK_comb _ h.1

/-- Relations not listed under `{c, d}` do not contain the monomial. -/
theorem psiZ_eq_zero (c d : Fin 14) (hcd : c ≤ d) (k : ℕ) (hk : k < 28) (hnot : k ∉ psiT c d) :
    psiZ k c d = 0 := by
  have hc := g2_psiComplete
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

theorem castQZ_psi (c d : Fin 14) (hcd : c ≤ d) (hnd : (psiT c d).Nodup)
    (hlt : ∀ k ∈ psiT c d, k < 28) :
    castQZ (S := G2sector) (combQ tabX ((psiT c d).map fun k => (196 + k, psiZ k c d))) =
      ∑ r, (qI r c d + qI r d c) • UD r := by
  rw [combQ, List.flatMap_map, castQZ_flatMap]
  rw [show (∑ r, (qI r c d + qI r d c) • UD r) =
    ∑ k ∈ Finset.range 28, (psiZ k c d) • castQZ (S := G2sector) (Uq k) from
      sum_option_idx (fun k => (psiZ k c d) • castQZ (S := G2sector) (Uq k))]
  have hsub : (psiT c d).toFinset ⊆ Finset.range 28 := by
    intro k hk; simpa using hlt k (List.mem_toFinset.mp hk)
  rw [← Finset.sum_subset hsub, List.sum_toFinset _ hnd]
  · congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [tabX, show ¬ (196 + k < 196) by omega, if_false, show 196 + k - 196 = k by omega,
      castQZ_smulQ]
  · intro k hk hnot
    rw [psiZ_eq_zero c d hcd k (by simpa using hk) (fun h => hnot (List.mem_toFinset.mpr h)),
      zero_smul]

theorem combQ_tabX (L : List (ℕ × ℤ)) (h : ∀ p ∈ L, p.1 < 196) : combQ tabX L = combQ tab L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [combQ, List.flatMap_cons] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [tabX, h p List.mem_cons_self]

theorem hVD (c d : Fin 14) (hcd : c ≤ d) :
    LevOK 4 0 (((48384 : ℕ) : ℤ) • symZ (S := G2sector) c d - ∑ r, (qI r c d + qI r d c) • UD r) := by
  have h := g2_symCheck' c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlev, hnd⟩, hlt⟩, hz⟩ := h
  have heq := castQZ_eq_of_enc (S := G2sector) (le_of_eq hnD) (encCheck_of_encLin hz)
  have hlev' := hlev
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlev'
  rw [symCertX, combQ, List.flatMap_append, ← combQ, ← combQ, castQZ_append,
    combQ_tabX _ fun p hp => (hlev' p hp).1, castQZ_psi c d hcd (by simpa using hnd) hlt,
    castQZ_smulQ, castQZ_symQ] at heq
  rw [show (((48384 : ℕ) : ℤ)) = 48384 from rfl, heq, add_sub_cancel_right]
  exact levOK_comb _ hlev

/-! ## The G2 divisor comparison -/

/-- **The G2 pair comparison.** -/
theorem g2_pairComparison : PairComparisonG G2sector :=
  pairComparisonG_of_cert (S := G2sector) qI hqD 4 18 48384 (by norm_num) (by norm_num) UD hAD hUD hVD

/-- **The G2 divisor comparison (B8 at `(Δ)`).** -/
theorem g2_divisorComparison : DivisorComparisonG G2sector :=
  divisorComparisonG_of_pair g2_pairComparison

/-- **The G2 sector fusion bound from U5 alone.** -/
theorem G2_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG G2sector F) :
    SectorFusionBound G2data F :=
  sectorFusionBoundG G2sector F hU5 g2_divisorComparison

end

end VOA.DeligneAudit.DeligneDivisor.G2

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.G2
#print axioms g2_pairComparison
#print axioms g2_divisorComparison
#print axioms G2_sectorFusionBound_of_U5
end AxiomAudit
