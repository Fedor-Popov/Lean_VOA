/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8DivisorChecks
import VOA.DeligneAudit.DeligneDivisorCol
import VOA.DeligneAudit.E8SectorData

/-!
# The E₈ divisor comparison

From the kernel-checked certificates of `E8DivisorChecks` and the generic assembly
(`pairComparisonG_of_cert`, `divisorComparisonG_of_pair`):

* **`e8_pairComparison : PairComparisonG E8sector`**;
* **`e8_divisorComparison : DivisorComparisonG E8sector`** (B8 at `(Δ)` for E₈);
* **`E8_sectorFusionBound_of_U5`**: `SectorFusionBound E8data F` from U5 alone.
-/

namespace VOA.DeligneAudit.DeligneDivisor.E8

open MvPolynomial VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneCarrier VOA.QuadraticJetCoefficientPairing
open VOA.DeligneAudit.DeligneCarrier.E8 (E8data E8sector)

noncomputable section

/-! ## The light-import copies agree with the generic checks -/

theorem nodeCheckCL_eq : @nodeCheckCL = @nodeCheckC := rfl
theorem colCheckL_eq : @colCheckL = @colCheck := rfl
theorem encLinL_eq : @encLinL = @encLin := rfl
theorem smulQL_eq : @smulQL = @smulQ := rfl
theorem qgetL_eq : @qgetL = @qget := rfl

theorem hn8 : E8sector.n = 248 := rfl

theorem hf8 : ∀ x c e, E8sector.f x c e = (fZ br x c e : ℂ) := fun _ _ _ => rfl

/-- Relation labels as indices (`none` = Casimir = `3875`). -/
def idx8 : Option (Fin 3875) → ℕ
  | none => 3875
  | some r => r

/-- Indices as relation labels. -/
def lab8 (s : ℕ) : Option (Fin 3875) := if h : s < 3875 then some ⟨s, h⟩ else none

theorem idx8_lab8 {s : ℕ} (hs : s < 3876) : idx8 (lab8 s) = s := by
  unfold lab8
  split_ifs with h
  · rfl
  · simp [idx8]; omega

theorem idx8_lt (r : Option (Fin 3875)) : idx8 r < 3876 := by
  cases r with
  | none => simp [idx8]
  | some r => simp only [idx8]; omega

theorem fullMatrix_eq8 (r : Option (Fin 3875)) :
    E8data.fullMatrix r = VOA.DeligneAudit.A2.entryMatrix (castL 248 (relZ8 (idx8 r))) := by
  cases r with
  | none => rfl
  | some r =>
      show VOA.DeligneAudit.DeligneCarrier.E8.rel r = _
      simp only [idx8, relZ8, r.2, if_true]
      rfl

theorem relZ8_range {k : ℕ} (hk : k < 3876) : ∀ t ∈ relZ8 k, t.1 < 248 ∧ t.2.1 < 248 := by
  have h := e8_relRange
  simp only [relRange8, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h k hk

/-! ## The tree -/

/-! ## The glued range checks, unpacked -/

theorem e8_node (i : ℕ) (h0 : 0 < i) (h1 : i < 61504) : nodeCheckC 248 colE8 tab par i = true := by
  rw [← nodeCheckCL_eq]; exact rangeAll_sound e8_nodeAll h0 h1

theorem e8_cols : ∀ x < 248, colCheck br colE8 248 x = true := fun _ hx => by
  rw [← colCheckL_eq]; exact rangeAll_sound e8_colAll (Nat.zero_le _) hx

theorem pair_div (c d : ℕ) (hd : d < 248) : (248 * c + d) / 248 = c := by omega

theorem pair_mod (c d : ℕ) (hd : d < 248) : (248 * c + d) % 248 = d := by omega

theorem e8_antiCheck' (c d : ℕ) (hc : c < 248) (hd : d < 248) (hcd : c < d) : antiCheck c d = true := by
  have h := rangeAll_sound e8_antiAll (i := 248 * c + d) (Nat.zero_le _) (by omega)
  simp only [antiP, pair_div c d hd, pair_mod c d hd, hcd, decide_true, Bool.not_true,
    Bool.false_or] at h
  exact h

theorem e8_symCheck' (c d : ℕ) (hc : c < 248) (hd : d < 248) (hcd : c ≤ d) : symCheck c d = true := by
  have h := rangeAll_sound e8_symAll (i := 248 * c + d) (Nat.zero_le _) (by omega)
  simp only [symP, pair_div c d hd, pair_mod c d hd, hcd, decide_true, Bool.not_true,
    Bool.false_or] at h
  exact h

theorem e8_UCheck (k : ℕ) (hk : k < 3876) : UCheck k = true :=
  rangeAll_sound e8_UAll (Nat.zero_le _) hk

/-! ## The tree -/

theorem e8_tree (i : ℕ) (hi : i < 61504) :
    LevOK (par i).2.2.2.1 (par i).2.2.2.2 (castQZ (S := E8sector) (tab i)) := by
  refine levOK_treeC hn8 hf8 e8_cols ?_ ?_ 61504 e8_node i hi
  · rw [e8_root.1]
    funext c d
    simp only [castQZ, qget_cons, qget_nil, add_zero, baseZ]
    have e : ∀ x : Fin E8sector.n, x = E8sector.c₀ ↔ (x : ℕ) = 247 :=
      fun x => ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have l : ∀ u v : ℕ, (247 = u ∧ 247 = v) ↔ (u = 247 ∧ v = 247) :=
      fun u v => ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
    simp only [l, e]
  · rw [e8_root.2]; exact ⟨rfl, rfl⟩

theorem e8_dep (i : ℕ) (hi : i < 61504) : (par i).2.2.2.1 ≤ 4 := by
  have h := rangeAll_sound e8_depthAll (Nat.zero_le _) hi
  simpa [depthP] using h

theorem levOK_comb {ℓ : ℕ} (L : List (ℕ × ℤ)) (h : levOf L ℓ = true) :
    LevOK 4 ℓ (castQZ (S := E8sector) (combQ tab L)) := by
  refine levOK_combQ tab L fun p hp => ?_
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h p hp
  exact levOK_mono (e8_tree p.1 h1) (e8_dep p.1 h1) h2

/-! ## Elementary tables -/

theorem castQZ_antiQ (c d : Fin 248) : castQZ (S := E8sector) (antiQ c d) = antiZ c d := by
  funext c' d'
  simp only [castQZ, antiQ, qget_cons, qget_nil, add_zero, antiZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]
  split_ifs <;> ring

theorem castQZ_symQ (c d : Fin 248) : castQZ (S := E8sector) (symQ c d) = symZ c d := by
  funext c' d'
  simp only [castQZ, symQ, qget_cons, qget_nil, add_zero, symZ, Fin.val_inj]
  have h1 : (c = c' ∧ d = d') ↔ (c' = c ∧ d' = d) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  have h2 : (d = c' ∧ c = d') ↔ (c' = d ∧ d' = c) :=
    ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩
  simp only [h1, h2]

theorem castQZ_flatMap {α : Type*} (L : List α) (F : α → QV) :
    castQZ (S := E8sector) (L.flatMap F) = (L.map fun x => castQZ (S := E8sector) (F x)).sum := by
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
    ∑ r : Option (Fin 3875), g (idx8 r) = ∑ k ∈ Finset.range 3876, g k := by
  have h1 : ∑ r : Option (Fin 3875), g (idx8 r) = g 3875 + ∑ i : Fin 3875, g i :=
    Fintype.sum_option _
  have h2 : ∑ i : Fin 3875, g i = ∑ k ∈ Finset.range 3875, g k := Fin.sum_univ_eq_sum_range g 3875
  have h3 : ∑ k ∈ Finset.range 3876, g k = ∑ k ∈ Finset.range 3875, g k + g 3875 :=
    Finset.sum_range_succ g 3875
  rw [h1, h2, h3, add_comm]

/-- Integer relation coefficients. -/
def qI (r : Option (Fin 3875)) (c d : Fin 248) : ℤ := qget (relZ8 (idx8 r)) c d

/-- The complement tables. -/
def U8 (r : Option (Fin 3875)) : ZTab E8sector := castQZ (Uq (idx8 r))

theorem entryMatrix_castL_apply (L : QV) (hL : ∀ t ∈ L, t.1 < 248 ∧ t.2.1 < 248) (c d : Fin 248) :
    VOA.DeligneAudit.A2.entryMatrix (castL 248 L) (c, d) = ((qget L c d : ℤ) : ℂ) := by
  induction L with
  | nil => simp [VOA.DeligneAudit.A2.entryMatrix, castL, qget]
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have ih' := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
    simp only [VOA.DeligneAudit.A2.entryMatrix, castL, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', qget_cons, Int.cast_add]
    congr 1
    have e1 : (Fin.ofNat 248 t.1 = c) ↔ t.1 = (c : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.1]
    have e2 : (Fin.ofNat 248 t.2.1 = d) ↔ t.2.1 = (d : ℕ) := by
      rw [Fin.ext_iff, Fin.val_ofNat, Nat.mod_eq_of_lt ht.2]
    have e : ((Fin.ofNat 248 t.1, Fin.ofNat 248 t.2.1) = (c, d)) ↔ (t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)) := by
      rw [Prod.mk.injEq]; exact and_congr e1 e2
    by_cases h : t.1 = (c : ℕ) ∧ t.2.1 = (d : ℕ)
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h, Int.cast_zero]

theorem hq8 (r : Option (Fin 3875)) (c d : Fin 248) :
    E8sector.fullMatrix r (c, d) = (qI r c d : ℂ) := by
  show E8data.fullMatrix r (c, d) = _
  rw [fullMatrix_eq8]
  exact entryMatrix_castL_apply _ (relZ8_range (idx8_lt r)) c d

/-! ## The certificates as `LevOK` facts -/

theorem hA8 (c d : Fin 248) (hcd : c < d) : LevOK 4 1 (((120 : ℕ) : ℤ) • antiZ (S := E8sector) c d) := by
  have h := e8_antiCheck' c d c.2 d.2 hcd
  simp only [antiCheck, Bool.and_eq_true] at h
  rw [encLinL_eq, smulQL_eq] at h
  have heq := castQZ_eq_of_enc (S := E8sector) (le_of_eq hn8) (encCheck_of_encLin h.2)
  rw [castQZ_smulQ, castQZ_antiQ] at heq
  rw [show (((120 : ℕ) : ℤ)) = 120 from rfl, heq]
  exact levOK_comb _ h.1

theorem hU8 (r : Option (Fin 3875)) : LevOK 4 2 (U8 r) := by
  have h := e8_UCheck (idx8 r) (idx8_lt r)
  simp only [UCheck, Bool.and_eq_true] at h
  rw [encLinL_eq] at h
  have heq := castQZ_eq_of_enc (S := E8sector) (le_of_eq hn8) (encCheck_of_encLin h.2)
  rw [U8, heq]
  exact levOK_comb _ h.1

/-- Relations not listed under `{c, d}` do not contain the monomial. -/
theorem psiZ_eq_zero (c d : Fin 248) (hcd : c ≤ d) (k : ℕ) (hk : k < 3876) (hnot : k ∉ psiT c d) :
    psiZ k c d = 0 := by
  have hc : ∀ k < 3876, ∀ t ∈ relZ8 k, k ∈ psiT (min t.1 t.2.1) (max t.1 t.2.1) := by
    intro k hk t ht
    have h := rangeAll_sound e8_psiAll (Nat.zero_le _) hk
    simp only [psiP, List.all_eq_true, decide_eq_true_eq] at h
    exact h t ht
  have hz : ∀ a b : ℕ, (a = c ∧ b = d) ∨ (a = d ∧ b = c) → qget (relZ8 k) a b = 0 := by
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
  rw [psiZ, qgetL_eq, hz c d (Or.inl ⟨rfl, rfl⟩), hz d c (Or.inr ⟨rfl, rfl⟩), add_zero]

theorem castQZ_psi (c d : Fin 248) (hcd : c ≤ d) (hnd : (psiT c d).Nodup)
    (hlt : ∀ k ∈ psiT c d, k < 3876) :
    castQZ (S := E8sector) (combQ tabX ((psiT c d).map fun k => (61504 + k, psiZ k c d))) =
      ∑ r, (qI r c d + qI r d c) • U8 r := by
  rw [combQ, List.flatMap_map, castQZ_flatMap]
  rw [show (∑ r, (qI r c d + qI r d c) • U8 r) =
    ∑ k ∈ Finset.range 3876, (psiZ k c d) • castQZ (S := E8sector) (Uq k) from
      sum_option_idx (fun k => (psiZ k c d) • castQZ (S := E8sector) (Uq k))]
  have hsub : (psiT c d).toFinset ⊆ Finset.range 3876 := by
    intro k hk; simpa using hlt k (List.mem_toFinset.mp hk)
  rw [← Finset.sum_subset hsub, List.sum_toFinset _ hnd]
  · congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [tabX, show ¬ (61504 + k < 61504) by omega, if_false, show 61504 + k - 61504 = k by omega,
      castQZ_smulQ]
  · intro k hk hnot
    rw [psiZ_eq_zero c d hcd k (by simpa using hk) (fun h => hnot (List.mem_toFinset.mpr h)),
      zero_smul]

theorem combQ_tabX (L : List (ℕ × ℤ)) (h : ∀ p ∈ L, p.1 < 61504) : combQ tabX L = combQ tab L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [combQ, List.flatMap_cons] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [tabX, h p List.mem_cons_self]

theorem hV8 (c d : Fin 248) (hcd : c ≤ d) :
    LevOK 4 0 (((96 : ℕ) : ℤ) • symZ (S := E8sector) c d - ∑ r, (qI r c d + qI r d c) • U8 r) := by
  have h := e8_symCheck' c d c.2 d.2 hcd
  simp only [symCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlev, hnd⟩, hlt⟩, hz⟩ := h
  rw [encLinL_eq, smulQL_eq] at hz
  have heq := castQZ_eq_of_enc (S := E8sector) (le_of_eq hn8) (encCheck_of_encLin hz)
  have hlev' := hlev
  simp only [levOf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlev'
  rw [symCertX, combQ, List.flatMap_append, ← combQ, ← combQ, castQZ_append,
    combQ_tabX _ fun p hp => (hlev' p hp).1, castQZ_psi c d hcd (by simpa using hnd) hlt,
    castQZ_smulQ, castQZ_symQ] at heq
  rw [show (((96 : ℕ) : ℤ)) = 96 from rfl, heq, add_sub_cancel_right]
  exact levOK_comb _ hlev

/-! ## The E₈ divisor comparison -/

/-- **The E₈ pair comparison.** -/
theorem e8_pairComparison : PairComparisonG E8sector :=
  pairComparisonG_of_cert (S := E8sector) qI hq8 4 120 96 (by norm_num) (by norm_num) U8 hA8 hU8 hV8

/-- **The E₈ divisor comparison (B8 at `(Δ)`).** -/
theorem e8_divisorComparison : DivisorComparisonG E8sector :=
  divisorComparisonG_of_pair e8_pairComparison

/-- **The E₈ sector fusion bound from U5 alone.** -/
theorem E8_sectorFusionBound_of_U5 (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBoundG E8sector F) :
    SectorFusionBound E8data F :=
  sectorFusionBoundG E8sector F hU5 e8_divisorComparison

end

end VOA.DeligneAudit.DeligneDivisor.E8

section AxiomAudit
open VOA.DeligneAudit.DeligneDivisor.E8
#print axioms e8_pairComparison
#print axioms e8_divisorComparison
#print axioms E8_sectorFusionBound_of_U5
end AxiomAudit
