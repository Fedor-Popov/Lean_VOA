/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorStable
import VOA.DeligneAudit.E6SectorChecksDiag
import VOA.DeligneAudit.E6SectorChecksTab

set_option linter.style.longLine false

/-!
# E₆ sector data: `c₀`, raising/Cartan/lowering tables, weights
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-! ## The coadjoint highest vector and the local Weyl data -/

theorem entryMatrix_toEntries_diag (l : List (ℕ × ℕ × ℤ)) (hl : inRange78 l = true)
    (h : l.all (fun t => !(t.1 == 77 && t.2.1 == 77)) = true) :
    A2.entryMatrix (toEntries l) ((77 : Fin 78), (77 : Fin 78)) = 0 := by
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
  have e1' : t.1 = 77 := by
    have := congrArg Fin.val e1; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.1] using this
  have e2' : t.2.1 = 77 := by
    have := congrArg Fin.val e2; simpa [Fin.ofNat, Nat.mod_eq_of_lt h2.2] using this
  simp [e1', e2'] at h1

theorem e6_diag : ∀ r, E6data.fullMatrix r ((77 : Fin 78), (77 : Fin 78)) = 0 := by
  intro r
  cases r with
  | none =>
    show A2.entryMatrix (toEntries qQ) _ = 0
    exact entryMatrix_toEntries_diag _ qQ_inRange diag_q_ok
  | some r =>
    show A2.entryMatrix (toEntries (relQ (show Fin 650 from r).val)) _ = 0
    have hall := diag_rel_ok
    have hr : (show Fin 650 from r).val < 650 := (show Fin 650 from r).2
    exact entryMatrix_toEntries_diag _ (List.all_eq_true.mp rel_inRange _ (List.mem_range.mpr hr))
      (List.all_eq_true.mp hall _ (List.mem_range.mpr hr))

theorem fE6_eq (x y c : Fin 78) : fE6 x y c = (coef (entry e6T x y) c : ℂ) := rfl

theorem e6_raising : ∀ e : Fin 78, (6 ≤ e.val ∧ e.val < 42) → ∀ y, fE6 e y 77 = 0 := by
  have h := raising_ok
  intro e he y
  have := List.all_eq_true.mp (List.all_eq_true.mp h e (List.mem_range'_1.mpr ⟨he.1, by omega⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE6_eq]; simpa using this


theorem e6_cartan : ∀ h : Fin 78, h.val < 6 → ∀ y : Fin 78,
    fE6 h y 77 = if y = (77 : Fin 78) then -(thetaH h : ℂ) else 0 := by
  have hc := cartan_ok
  intro h hh y
  have := List.all_eq_true.mp (List.all_eq_true.mp hc h (List.mem_range.mpr hh)) y (List.mem_range.mpr y.2)
  simp only [beq_iff_eq] at this
  have hmod : (⟨h.val % 78, Nat.mod_lt _ (by norm_num)⟩ : Fin 78) = h := Fin.ext (Nat.mod_eq_of_lt h.2)
  rw [hmod] at this
  rw [fE6_eq, show ((77 : Fin 78) : ℕ) = 77 from rfl, this]
  by_cases hy : y = (77 : Fin 78)
  · subst hy; simp
  · have : (y : ℕ) ≠ 77 := fun h' => hy (Fin.ext h')
    simp [hy, this]

/-! ## Weights -/

theorem e6_table_wt : ∀ x y c, wtE6 c ≠ wtE6 x + wtE6 y → fE6 x y c = 0 := by
  intro x y c hne
  have hx : x.val < 78 := x.2
  have hchunk : ∃ lo hi, lo ≤ x.val ∧ x.val < hi ∧ wtChunk lo hi = true := by
    rcases (show (0 ≤ x.val ∧ x.val < 13) ∨ (13 ≤ x.val ∧ x.val < 26) ∨ (26 ≤ x.val ∧ x.val < 39) ∨ (39 ≤ x.val ∧ x.val < 52) ∨ (52 ≤ x.val ∧ x.val < 65) ∨ (65 ≤ x.val ∧ x.val < 78) by omega) with h | h | h | h | h | h
    · exact ⟨0, 13, h.1, h.2, wtChunk_0⟩
    · exact ⟨13, 26, h.1, h.2, wtChunk_1⟩
    · exact ⟨26, 39, h.1, h.2, wtChunk_2⟩
    · exact ⟨39, 52, h.1, h.2, wtChunk_3⟩
    · exact ⟨52, 65, h.1, h.2, wtChunk_4⟩
    · exact ⟨65, 78, h.1, h.2, wtChunk_5⟩
  obtain ⟨lo, hi, h1, h2, hc⟩ := hchunk
  unfold wtChunk at hc
  have hrow := List.all_eq_true.mp (List.all_eq_true.mp hc x (List.mem_range'_1.mpr ⟨h1, by omega⟩)) y
    (List.mem_range.mpr y.2)
  rw [fE6_eq]
  norm_cast
  unfold coef
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  have hpp := List.all_eq_true.mp hrow p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpp
  split_ifs with hpc
  · exfalso; apply hne
    funext k
    have := List.all_eq_true.mp hpp.2 k (List.mem_range.mpr k.2)
    simp only [beq_iff_eq] at this
    simp only [wtE6, Pi.add_apply]
    rw [← hpc]; exact this
  · rfl

/-- **No `m`-fold weight sum hits `m·wt c₀ - (m e + 1)·wt i`**, when weights lie in `-θ + Q⁺` and the
`α_k`-string through `-θ` has length `e`. -/
theorem noweight_of (c₀ : Fin 78) (hc₀ : wtE6 c₀ = -thetaV) (hpos : ∀ y k, 0 ≤ wtE6 y k + thetaV k)
    (i : Fin 78) (k₀ : Fin 6) (hi : wtE6 i = -Pi.single k₀ 1) (e : ℕ)
    (hstr : ∀ y, (∀ k, k ≠ k₀ → wtE6 y k + thetaV k = 0) → wtE6 y k₀ + thetaV k₀ ≤ e)
    (m : ℕ) (t : Fin m → Fin 78) :
    ∑ j, wtE6 (t j) ≠ m • wtE6 c₀ - (m * e + 1) • wtE6 i := by
  intro h
  have hk : ∀ k, ∑ j, (wtE6 (t j) k + thetaV k) = (m * e + 1 : ℕ) * (Pi.single k₀ 1 : Fin 6 → ℤ) k := by
    intro k
    have := congrFun h k
    rw [hc₀, hi] at this
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at this
    rw [Finset.sum_add_distrib, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hzero : ∀ j, ∀ k, k ≠ k₀ → wtE6 (t j) k + thetaV k = 0 := by
    intro j k hkk
    have h0 := hk k
    rw [Pi.single_eq_of_ne hkk, mul_zero] at h0
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos (t j) k)).mp h0 j (Finset.mem_univ _)
  have hle : ∑ j, (wtE6 (t j) k₀ + thetaV k₀) ≤ ∑ _j : Fin m, (e : ℤ) :=
    Finset.sum_le_sum fun j _ => hstr (t j) (hzero j)
  rw [hk k₀, Pi.single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  push_cast at hle
  nlinarith


theorem e6_noweight : ∀ i : Fin 78, (i.val ∈ [47, 46, 45, 44, 43, 42]) → ∀ (m : ℕ) (t : Fin m → Fin 78),
    ∑ j, wtE6 (t j) ≠ m • wtE6 77 - (m * lowExpE6 i + 1) • wtE6 i := by
  intro i hi m t
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h
  · have : i = 47 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 47 0 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 46 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 46 1 (by decide +kernel) 1 (by decide +kernel) m t
  · have : i = 45 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 45 2 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 44 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 44 3 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 43 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 43 4 (by decide +kernel) 0 (by decide +kernel) m t
  · have : i = 42 := Fin.ext h
    subst this
    exact noweight_of 77 (by decide +kernel) e6_wt_pos 42 5 (by decide +kernel) 0 (by decide +kernel) m t


end

end VOA.DeligneAudit.DeligneCarrier.E6
