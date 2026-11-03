/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7DivisorChecks
import VOA.DeligneAudit.DeligneDivisorCol
import VOA.DeligneAudit.E7SectorData
import VOA.DeligneAudit.DeligneDivisorSparse

/-!
# The E₇ divisor comparison

From the kernel-checked certificates of `E7DivisorChecks` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`e7_pairComparison : PairComparisonG E7sector`**;
* **`e7_divisorComparison : DivisorComparisonG E7sector`** (B8 at `(Δ)` for E₇);
* **`E7_sectorFusionBound_of_U5`**: `SectorFusionBound E7data F` from U5 alone.
-/

namespace VOA.DeligneAudit.DeligneDivisor.E7

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneCarrier.E7 (E7data E7sector)

noncomputable section

theorem hn7 : E7sector.n = 133 := rfl

theorem hf7 : ∀ x c e, E7sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-- Relation labels as indices (`none` = Casimir = `1539`). -/
def idx7 : Option (Fin 1539) → ℕ
  | none => 1539
  | some r => r

/-- Indices as relation labels. -/
def lab7 (s : ℕ) : Option (Fin 1539) := if h : s < 1539 then some ⟨s, h⟩ else none

theorem idx7_lab7 {s : ℕ} (hs : s < 1540) : idx7 (lab7 s) = s := by
  unfold lab7
  split_ifs with h
  · rfl
  · simp [idx7]; omega

theorem idx7_lt (r : Option (Fin 1539)) : idx7 r < 1540 := by
  cases r with
  | none => simp [idx7]
  | some r => simp only [idx7]; omega

theorem fullMatrix_eq7 (r : Option (Fin 1539)) :
    E7data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 133 (relZ7 (idx7 r))) := by
  cases r with
  | none => rfl
  | some r =>
      show VOA.DeligneAudit.DeligneCarrier.E7.rel r = _
      simp only [idx7, relZ7, r.2, if_true]
      rfl

theorem relZ7_range {k : ℕ} (hk : k < 1540) : ∀ t ∈ relZ7 k, t.1 < 133 ∧ t.2.1 < 133 := by
  have h := e7_relRange
  simp only [relRange7, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

/-! ## The tree -/

/-! ## The glued range checks, unpacked -/

theorem e7_node (i : ℕ) (h0 : 0 < i) (h1 : i < 17689) : nodeCheckC 133 colE7 tab par i = true :=
  rangeAll_sound e7_nodeAll h0 h1

theorem e7_cols : ∀ x < 133, colCheck br colE7 133 x = true := fun _ hx =>
  rangeAll_sound e7_colAll (Nat.zero_le _) hx

theorem pair_div (c d : ℕ) (hd : d < 133) : (133 * c + d) / 133 = c := by omega

theorem pair_mod (c d : ℕ) (hd : d < 133) : (133 * c + d) % 133 = d := by omega

theorem e7_antiCheck' (c d : ℕ) (hc : c < 133) (hd : d < 133) (hcd : c < d) : antiCheck c d = true := by
  have h := rangeAll_sound e7_antiAll (i := 133 * c + d) (Nat.zero_le _) (by omega)
  simp only [antiP, pair_div c d hd, pair_mod c d hd, hcd, decide_true, Bool.not_true,
    Bool.false_or] at h
  exact h

theorem e7_symCheck' (c d : ℕ) (hc : c < 133) (hd : d < 133) (hcd : c ≤ d) : symCheck c d = true := by
  have h := rangeAll_sound e7_symAll (i := 133 * c + d) (Nat.zero_le _) (by omega)
  simp only [symP, pair_div c d hd, pair_mod c d hd, hcd, decide_true, Bool.not_true,
    Bool.false_or] at h
  exact h

theorem e7_UCheck (k : ℕ) (hk : k < 1540) : UCheck k = true :=
  rangeAll_sound e7_UAll (Nat.zero_le _) hk

/-! ## The tree -/

theorem e7_tree (i : ℕ) (hi : i < 17689) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := E7sector) (tab i)) := by
  refine levOK_treeC hn7 hf7 e7_cols ?_ ?_ 17689 e7_node i hi
  · rw [e7_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin E7sector.n, x = E7sector.c₀ ↔ (x : ℕ) = 132 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (132 = u ∧ 132 = v) ↔ (u = 132 ∧ v = 132) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [e7_root.2]; exact ⟨rfl, rfl⟩

theorem e7_dep (i : ℕ) (hi : i < 17689) : (par i).2.2.2.1 ≤ 4 := by
  have h := rangeAll_sound e7_depthAll (Nat.zero_le _) hi
  simpa [depthP] using h

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := E7sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (e7_tree p.1 h1) (e7_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 133) : castQZ (S := E7sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 133) : castQZ (S := E7sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := E7sector) (L.flatMap F) = (L.map fun x => castQZ (S := E7sector) (F x)).sum := by
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
    ∑ r : Option (Fin 1539), g (idx7 r) = ∑ k ∈ Finset.range 1540, g k := by
  have h1 : ∑ r : Option (Fin 1539), g (idx7 r) = g 1539 + ∑ i : Fin 1539, g i :=
    Fintype.sum_option _
  have h2 : ∑ i : Fin 1539, g i = ∑ k ∈ Finset.range 1539, g k := Fin.sum_univ_eq_sum_range g 1539
  have h3 : ∑ k ∈ Finset.range 1540, g k = ∑ k ∈ Finset.range 1539, g k + g 1539 :=
    Finset.sum_range_succ g 1539
  rw [h1, h2, h3, add_comm]

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 1539)) (c d : Fin 133) : ℤ := qget (relZ7 (idx7 r)) c d

/-- The complement tables. -/
def U7 (r : Option (Fin 1539)) : ZTab E7sector := castQZ (Uq (idx7 r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 133 ∧ t.2.1 < 133) (c d : Fin 133) :
    VOA.DeligneAudit.A2.entryMatrix (castL 133 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 133 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 133 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 133 t.1, Fin.ofNat 133 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hq7 (r : Option (Fin 1539)) (c d : Fin 133) :
    E7sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show E7data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq7]
  exact entryMatrix_castL_apply _ (relZ7_range (idx7_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem hA7 (c d : Fin 133) (hcd : c < d) : LevOK 4 1 (((24 : ℕ) : ℤ) • antiZ (S := E7sector) c d) := by
  have h := e7_antiCheck' c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := E7sector) (le_of_eq hn7) (encCheck_of_encLin h.2)
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((24 : ℕ) : ℤ)) = 24 from rfl, heq]
  exact levOK_comb _ h.1

theorem hU7 (r : Option (Fin 1539)) : LevOK 4 2 (U7 r) := by
  have h := e7_UCheck (idx7 r) (idx7_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  have heq := castQZ_eq_of_enc (S := E7sector) (le_of_eq hn7) (encCheck_of_encLin h.2)
  rw [U7, heq]
  exact levOK_comb _ h.1

/-- Relations not listed under `{c, d}` do not contain the monomial. -/
theorem psiZ_eq_zero (c d : Fin 133) (hcd : c ≤ d) (k : ℕ) (hk : k < 1540) (hnot : k ∉ psiT c d) :
    psiZ k c d = 0 := by
  have hc : ∀ k < 1540, ∀ t ∈ relZ7 k, k ∈ psiT (min t.1 t.2.1) (max t.1 t.2.1) := by
    intro k hk t ht
    have h := rangeAll_sound e7_psiAll (Nat.zero_le _) hk
    simp only [psiP, List.all_eq_true, decide_eq_true_eq] at h
    exact h t ht
  have hz : ∀ a b : ℕ, (a = c ∧ b = d) ∨ (a = d ∧ b = c) → qget (relZ7 k) a b = 0 := by
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

theorem castQZ_psi (c d : Fin 133) (hcd : c ≤ d) (hnd : (psiT c d).Nodup)
    (hlt : ∀ k ∈ psiT c d, k < 1540) :
    castQZ (S := E7sector) (combQ tabX ((psiT c d).map fun k => (17689 + k, psiZ k c d))) =
      ∑ r, (qI r c d + qI r d c) • U7 r := by
  rw [combQ, List.flatMap_map, castQZ_flatMap]
  rw [show (∑ r, (qI r c d + qI r d c) • U7 r) =
    ∑ k ∈ Finset.range 1540, (psiZ k c d) • castQZ (S := E7sector) (Uq k) from
      sum_option_idx (fun k => (psiZ k c d) • castQZ (S := E7sector) (Uq k))]
  have hsub : (psiT c d).toFinset ⊆ Finset.range 1540 := by
    intro k hk; simpa using hlt k (List.mem_toFinset.mp hk)
  rw [← Finset.sum_subset hsub, List.sum_toFinset _ hnd]
  · congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [tabX, show ¬ (17689 + k < 17689) by omega, if_false, show 17689 + k - 17689 = k by omega,
      castQZ_smulQ]
  · intro k hk hnot
    rw [psiZ_eq_zero c d hcd k (by simpa using hk) (fun h => hnot (List.mem_toFinset.mpr h)),
      zero_smul]

theorem combQ_tabX (L : List (ℕ × ℤ)) (h : ∀ p ∈ L, p.1 < 17689) : combQ tabX L = combQ tab L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [combQ, List.flatMap_cons] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [tabX, h p List.mem_cons_self]

theorem hV7 (c d : Fin 133) (hcd : c ≤ d) :
    LevOK 4 0 (((672 : ℕ) : ℤ) • symZ (S := E7sector) c d - ∑ r, (qI r c d + qI r d c) • U7 r) := by
  have h := e7_symCheck' c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlev, hnd⟩, hlt⟩, hz⟩ := h
  have heq := castQZ_eq_of_enc (S := E7sector) (le_of_eq hn7) (encCheck_of_encLin hz)
  have hlev' := hlev
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlev'
  rw [symCertX, combQ, List.flatMap_append, ← combQ, ← combQ, castQZ_append,
    combQ_tabX _ fun p hp => (hlev' p hp).1, castQZ_psi c d hcd (by simpa using hnd) hlt,
    castQZ_smulQ, castQZ_symQ] at heq
  rw [show (((672 : ℕ) : ℤ)) = 672 from rfl, heq, add_sub_cancel_right]
  exact levOK_comb _ hlev

/-! ## The E₇ divisor comparison -/

/-- **The E₇ pair comparison.** -/
theorem e7_pairComparison : PairComparisonG E7sector :=
  pairComparisonG_of_cert (S := E7sector) qI hq7 4 24 672 (by norm_num) (by norm_num) U7 hA7 hU7 hV7

/-- **The E₇ divisor comparison (B8 at `(Δ)`).** -/
theorem e7_divisorComparison : DivisorComparisonG E7sector :=
  divisorComparisonG_of_pair e7_pairComparison

/-- **The E₇ sector fusion bound from U5 alone.** -/
theorem E7_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG E7sector F) :
    SectorFusionBound E7data F :=
  sectorFusionBoundG E7sector F hU5 e7_divisorComparison

end

end VOA.DeligneAudit.DeligneDivisor.E7

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.E7
#print axioms e7_pairComparison
#print axioms e7_divisorComparison
#print axioms E7_sectorFusionBound_of_U5
end AxiomAudit
