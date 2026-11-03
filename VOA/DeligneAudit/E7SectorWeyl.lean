/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStable

/-!
# `E₇` sector data: `c₀ = 132` (weight `-θ`), raising/Cartan/lowering tables, weights
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E7

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem entryMatrix_toEntries_diag (l : List (ℕ × ℕ × ℤ)) (hl : inRange133 l = true)
    (h : l.all (fun t => !(t.1 == 132 && t.2.1 == 132)) = true) :
    A2.entryMatrix (toEntries l) ((132 : Fin 133), (132 : Fin 133)) = 0 := by
  unfold A2.entryMatrix toEntries
  rw [List.map_map]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  have h1 := List.all_eq_true.mp h t ht
  have h2 := List.all_eq_true.mp hl t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  simp only [Function.comp_apply, ite_eq_right_iff, Prod.mk.injEq, and_imp]
  intro e1 e2
  exfalso
  have e1' : t.1 = 132 := by
    have := congrArg Fin.val e1; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.1] using this
  have e2' : t.2.1 = 132 := by
    have := congrArg Fin.val e2; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.2] using this
  simp [e1', e2'] at h1

theorem e7_diag : ∀ r, E7data.fullMatrix r ((132 : Fin 133), (132 : Fin 133)) = 0 := by
  intro r
  cases r with
  | none =>
    show A2.entryMatrix (toEntries qQ) _ = 0
    exact entryMatrix_toEntries_diag _ qQ_inRange diag_q_ok
  | some r =>
    show A2.entryMatrix (toEntries (relQ (show Fin 1539 from r).val)) _ = 0
    have hall := diag_rel_ok
    have hr : (show Fin 1539 from r).val < 1539 := (show Fin 1539 from r).2
    exact entryMatrix_toEntries_diag _ (List.all_eq_true.mp rel_inRange _ (List.mem_range.mpr hr))
      (List.all_eq_true.mp hall _ (List.mem_range.mpr hr))

theorem fE7_eq (x y c : Fin 133) : fE7 x y c = (coef (entry e7T x y) c : ℂ) := rfl

theorem e7_raising : ∀ e : Fin 133, (7 ≤ e.val ∧ e.val < 70) → ∀ y, fE7 e y 132 = 0 := by
  have h := raising_ok
  intro e he y
  have := List.all_eq_true.mp (List.all_eq_true.mp h e (List.mem_range'_1.mpr ⟨he.1, by omega⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE7_eq]; simpa using this

theorem e7_cartan : ∀ h : Fin 133, h.val < 7 → ∀ y : Fin 133,
    fE7 h y 132 = if y = (132 : Fin 133) then -(thetaH h : ℂ) else 0 := by
  have hc := cartan_ok
  intro h hh y
  have := List.all_eq_true.mp (List.all_eq_true.mp hc h (List.mem_range.mpr hh)) y (List.mem_range.mpr y.2)
  simp only [beq_iff_eq] at this
  have hmod : (⟨h.val % 133, Nat.mod_lt _ (by norm_num)⟩ : Fin 133) = h := Fin.ext (Nat.mod_eq_of_lt h.2)
  rw [hmod] at this
  rw [fE7_eq, show ((132 : Fin 133) : ℕ) = 132 from rfl, this]
  by_cases hy : y = (132 : Fin 133)
  · subst hy; simp
  · have : (y : ℕ) ≠ 132 := fun h' => hy (Fin.ext h')
    simp [hy, this]

/-! ## Weights -/

theorem e7_table_wt : ∀ x y c, E7Lie.wt c ≠ E7Lie.wt x + E7Lie.wt y → fE7 x y c = 0 := by
  intro x y c hne
  have hx : x.val < 133 := x.2
  have hchunk : ∃ lo hi, lo ≤ x.val ∧ x.val < hi ∧ wtChunk lo hi = true := by
    rcases (show (0 ≤ x.val ∧ x.val < 19) ∨ (19 ≤ x.val ∧ x.val < 38) ∨ (38 ≤ x.val ∧ x.val < 57) ∨
        (57 ≤ x.val ∧ x.val < 76) ∨ (76 ≤ x.val ∧ x.val < 95) ∨ (95 ≤ x.val ∧ x.val < 114) ∨
        (114 ≤ x.val ∧ x.val < 133) by omega) with h | h | h | h | h | h | h
    · exact ⟨0, 19, h.1, h.2, wtChunk_0⟩
    · exact ⟨19, 38, h.1, h.2, wtChunk_1⟩
    · exact ⟨38, 57, h.1, h.2, wtChunk_2⟩
    · exact ⟨57, 76, h.1, h.2, wtChunk_3⟩
    · exact ⟨76, 95, h.1, h.2, wtChunk_4⟩
    · exact ⟨95, 114, h.1, h.2, wtChunk_5⟩
    · exact ⟨114, 133, h.1, h.2, wtChunk_6⟩
  obtain ⟨lo, hi, h1, h2, hc⟩ := hchunk
  unfold wtChunk at hc
  have hrow := List.all_eq_true.mp (List.all_eq_true.mp hc x (List.mem_range'_1.mpr ⟨h1, by omega⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE7_eq]
  norm_cast
  unfold coef
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  have hpp := List.all_eq_true.mp hrow p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpp
  split_ifs with hpc
  · exfalso; apply hne
    obtain ⟨_, hp2⟩ := hpp
    have hw := wtLink
    unfold wtLinkOK at hw
    have wx := beq_iff_eq.mp (List.all_eq_true.mp hw x (List.mem_finRange x))
    have wy := beq_iff_eq.mp (List.all_eq_true.mp hw y (List.mem_finRange y))
    have wc := beq_iff_eq.mp (List.all_eq_true.mp hw c (List.mem_finRange c))
    have e2 := beq_iff_eq.mp hp2
    rw [hpc, ← wx, ← wy, ← wc] at e2
    funext k
    have := congrArg (fun l => l.getD k.val 0) e2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_zipWith] at this
    simpa [Fin.is_lt] using this
  · rfl

/-- **No `m`-fold weight sum hits `m·wt c₀ - (m e + 1)·wt i`**. -/
theorem noweight_of (c₀ : Fin 133) (hc₀ : E7Lie.wt c₀ = -thetaV)
    (hpos : ∀ y k, 0 ≤ E7Lie.wt y k + thetaV k)
    (i : Fin 133) (k₀ : Fin 7) (hi : E7Lie.wt i = -Pi.single k₀ 1) (e : ℕ)
    (hstr : ∀ y, (∀ k, k ≠ k₀ → E7Lie.wt y k + thetaV k = 0) → E7Lie.wt y k₀ + thetaV k₀ ≤ e)
    (m : ℕ) (t : Fin m → Fin 133) :
    ∑ j, E7Lie.wt (t j) ≠ m • E7Lie.wt c₀ - (m * e + 1) • E7Lie.wt i := by
  intro h
  have hk : ∀ k, ∑ j, (E7Lie.wt (t j) k + thetaV k) = (m * e + 1 : ℕ) * (Pi.single k₀ 1 : Fin 7 → ℤ) k := by
    intro k
    have := congrFun h k
    rw [hc₀, hi] at this
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at this
    rw [Finset.sum_add_distrib, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hzero : ∀ j, ∀ k, k ≠ k₀ → E7Lie.wt (t j) k + thetaV k = 0 := by
    intro j k hkk
    have h0 := hk k
    rw [Pi.single_eq_of_ne hkk, mul_zero] at h0
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos (t j) k)).mp h0 j (Finset.mem_univ _)
  have hle : ∑ j, (E7Lie.wt (t j) k₀ + thetaV k₀) ≤ ∑ _j : Fin m, (e : ℤ) :=
    Finset.sum_le_sum fun j _ => hstr (t j) (hzero j)
  rw [hk k₀, Pi.single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  push_cast at hle
  nlinarith

theorem e7_noweight : ∀ i : Fin 133, (i.val ∈ [76, 75, 74, 73, 72, 71, 70]) → ∀ (m : ℕ) (t : Fin m → Fin 133),
    ∑ j, E7Lie.wt (t j) ≠ m • E7Lie.wt 132 - (m * lowExpE7 i + 1) • E7Lie.wt i := by
  intro i hi m t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h
  · have : i = 76 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 76 0 (by decide +kernel) 1 (by decide +kernel) m t
  · have : i = 75 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 75 1 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 74 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 74 2 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 73 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 73 3 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 72 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 72 4 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 71 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 71 5 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 70 := Fin.ext h
    subst this
    exact noweight_of 132 (by decide +kernel) e7_wt_pos 70 6 (by decide +kernel) 0 (by decide +kernel) m t

end

end VOA.DeligneAudit.DeligneCarrier.E7
