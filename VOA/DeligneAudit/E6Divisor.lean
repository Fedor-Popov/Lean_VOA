/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorChecksA3
import VOA.DeligneAudit.E6DivisorChecksB
import VOA.DeligneAudit.E6DivisorChecksC
import VOA.DeligneAudit.DeligneDivisorCol
import VOA.DeligneAudit.E6SectorData
import VOA.DeligneAudit.DeligneDivisorSparse

/-!
# The E₆ divisor comparison

From the kernel-checked certificates of `E6DivisorChecks*` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`e6_pairComparison : PairComparisonG E6sector`**;
* **`e6_divisorComparison : DivisorComparisonG E6sector`** (B8 at `(Δ)` for E₆);
* **`E6_sectorFusionBound_of_U5`**: `SectorFusionBound E6data F` from U5 alone.
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneCarrier.E6 (E6data E6sector)

noncomputable section

theorem hn6 : E6sector.n = 78 := rfl

theorem hf6 : ∀ x c e, E6sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-- Relation labels as indices (`none` = Casimir = `650`). -/
def idx6 : Option (Fin 650) → ℕ
  | none => 650
  | some r => r

/-- Indices as relation labels. -/
def lab6 (s : ℕ) : Option (Fin 650) := if h : s < 650 then some ⟨s, h⟩ else none

theorem idx6_lab6 {s : ℕ} (hs : s < 651) : idx6 (lab6 s) = s := by
  unfold lab6
  split_ifs with h
  · rfl
  · simp [idx6]; omega

theorem idx6_lt (r : Option (Fin 650)) : idx6 r < 651 := by
  cases r with
  | none => simp [idx6]
  | some r => simp only [idx6]; omega

theorem fullMatrix_eq6 (r : Option (Fin 650)) :
    E6data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 78 (relZ6 (idx6 r))) := by
  cases r with
  | none => rfl
  | some r =>
      show VOA.DeligneAudit.DeligneCarrier.E6.rel r = _
      simp only [idx6, relZ6, r.2, if_true]
      rfl

theorem relZ6_range {k : ℕ} (hk : k < 651) : ∀ t ∈ relZ6 k, t.1 < 78 ∧ t.2.1 < 78 := by
  have h := e6_relRange
  simp only [relRange6, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

/-! ## The tree -/

theorem e6_cols : ∀ x < 78, colCheck br colE6 78 x = true := by
  have h := e6_colChecks
  simp only [colChecks, List.all_eq_true, List.mem_range] at h
  exact h

theorem e6_tree (i : ℕ) (hi : i < 6084) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := E6sector) (tab i)) := by
  refine levOK_treeC hn6 hf6 e6_cols ?_ ?_ 6084 e6_node i hi
  · rw [e6_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin E6sector.n, x = E6sector.c₀ ↔ (x : ℕ) = 77 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (77 = u ∧ 77 = v) ↔ (u = 77 ∧ v = 77) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [e6_root.2]; exact ⟨rfl, rfl⟩

theorem e6_dep (i : ℕ) (hi : i < 6084) : (par i).2.2.2.1 ≤ 4 := by
  have h := e6_depth
  simp only [depthCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := E6sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (e6_tree p.1 h1) (e6_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 78) : castQZ (S := E6sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 78) : castQZ (S := E6sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := E6sector) (L.flatMap F) = (L.map fun x => castQZ (S := E6sector) (F x)).sum := by
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
    ∑ r : Option (Fin 650), g (idx6 r) = ∑ k ∈ Finset.range 651, g k := by
  have h1 : ∑ r : Option (Fin 650), g (idx6 r) = g 650 + ∑ i : Fin 650, g i :=
    Fintype.sum_option _
  have h2 : ∑ i : Fin 650, g i = ∑ k ∈ Finset.range 650, g k := Fin.sum_univ_eq_sum_range g 650
  have h3 : ∑ k ∈ Finset.range 651, g k = ∑ k ∈ Finset.range 650, g k + g 650 :=
    Finset.sum_range_succ g 650
  rw [h1, h2, h3, add_comm]

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 650)) (c d : Fin 78) : ℤ := qget (relZ6 (idx6 r)) c d

/-- The complement tables. -/
def U6 (r : Option (Fin 650)) : ZTab E6sector := castQZ (Uq (idx6 r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 78 ∧ t.2.1 < 78) (c d : Fin 78) :
    VOA.DeligneAudit.A2.entryMatrix (castL 78 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 78 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 78 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 78 t.1, Fin.ofNat 78 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hq6 (r : Option (Fin 650)) (c d : Fin 78) :
    E6sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show E6data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq6]
  exact entryMatrix_castL_apply _ (relZ6_range (idx6_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem hA6 (c d : Fin 78) (hcd : c < d) : LevOK 4 1 (((12 : ℕ) : ℤ) • antiZ (S := E6sector) c d) := by
  have h := e6_antiCheck' c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := E6sector) (le_of_eq hn6) (encCheck_of_encLin h.2)
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((12 : ℕ) : ℤ)) = 12 from rfl, heq]
  exact levOK_comb _ h.1

theorem hU6 (r : Option (Fin 650)) : LevOK 4 2 (U6 r) := by
  have h := e6_UCheck (idx6 r) (idx6_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := E6sector) (le_of_eq hn6) (encCheck_of_encLin h.2)
  rw [U6, heq]
  exact levOK_comb _ h.1

/-- Relations not listed under `{c, d}` do not contain the monomial. -/
theorem psiZ_eq_zero (c d : Fin 78) (hcd : c ≤ d) (k : ℕ) (hk : k < 651) (hnot : k ∉ psiT c d) :
    psiZ k c d = 0 := by
  have hc := e6_psiComplete
  simp only [psiComplete, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  have hz : ∀ a b : ℕ, (a = c ∧ b = d) ∨ (a = d ∧ b = c) → qget (relZ6 k) a b = 0 := by
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

theorem castQZ_psi (c d : Fin 78) (hcd : c ≤ d) (hnd : (psiT c d).Nodup)
    (hlt : ∀ k ∈ psiT c d, k < 651) :
    castQZ (S := E6sector) (combQ tabX ((psiT c d).map fun k => (6084 + k, psiZ k c d))) =
      ∑ r, (qI r c d + qI r d c) • U6 r := by
  rw [combQ, List.flatMap_map, castQZ_flatMap]
  rw [show (∑ r, (qI r c d + qI r d c) • U6 r) =
    ∑ k ∈ Finset.range 651, (psiZ k c d) • castQZ (S := E6sector) (Uq k) from
      sum_option_idx (fun k => (psiZ k c d) • castQZ (S := E6sector) (Uq k))]
  have hsub : (psiT c d).toFinset ⊆ Finset.range 651 := by
    intro k hk; simpa using hlt k (List.mem_toFinset.mp hk)
  rw [← Finset.sum_subset hsub, List.sum_toFinset _ hnd]
  · congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [tabX, show ¬ (6084 + k < 6084) by omega, if_false, show 6084 + k - 6084 = k by omega,
      castQZ_smulQ]
  · intro k hk hnot
    rw [psiZ_eq_zero c d hcd k (by simpa using hk) (fun h => hnot (List.mem_toFinset.mpr h)),
      zero_smul]

theorem combQ_tabX (L : List (ℕ × ℤ)) (h : ∀ p ∈ L, p.1 < 6084) : combQ tabX L = combQ tab L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [combQ, List.flatMap_cons] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [tabX, h p List.mem_cons_self]

theorem hV6 (c d : Fin 78) (hcd : c ≤ d) :
    LevOK 4 0 (((216 : ℕ) : ℤ) • symZ (S := E6sector) c d - ∑ r, (qI r c d + qI r d c) • U6 r) := by
  have h := e6_symCheck' c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlev, hnd⟩, hlt⟩, hz⟩ := h
  have heq := castQZ_eq_of_enc (S := E6sector) (le_of_eq hn6) (encCheck_of_encLin hz)
  have hlev' := hlev
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlev'
  rw [symCertX, combQ, List.flatMap_append, ← combQ, ← combQ, castQZ_append,
    combQ_tabX _ fun p hp => (hlev' p hp).1, castQZ_psi c d hcd (by simpa using hnd) hlt,
    castQZ_smulQ, castQZ_symQ] at heq
  rw [show (((216 : ℕ) : ℤ)) = 216 from rfl, heq, add_sub_cancel_right]
  exact levOK_comb _ hlev

/-! ## The E₆ divisor comparison -/

/-- **The E₆ pair comparison.** -/
theorem e6_pairComparison : PairComparisonG E6sector :=
  pairComparisonG_of_cert (S := E6sector) qI hq6 4 12 216 (by norm_num) (by norm_num) U6 hA6 hU6 hV6

/-- **The E₆ divisor comparison (B8 at `(Δ)`).** -/
theorem e6_divisorComparison : DivisorComparisonG E6sector :=
  divisorComparisonG_of_pair e6_pairComparison

/-- **The E₆ sector fusion bound from U5 alone.** -/
theorem E6_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG E6sector F) :
    SectorFusionBound E6data F :=
  sectorFusionBoundG E6sector F hU5 e6_divisorComparison

end

end VOA.DeligneAudit.DeligneDivisor.E6

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.E6
#print axioms e6_pairComparison
#print axioms e6_divisorComparison
#print axioms E6_sectorFusionBound_of_U5
end AxiomAudit
