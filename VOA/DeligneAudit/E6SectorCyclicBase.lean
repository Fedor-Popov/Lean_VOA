/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorStable

set_option linter.style.longLine false

/-!
# E₆ sector data: coadjoint words on sparse vectors
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-! ## Coadjoint cyclicity -/

theorem wordA_single (l : List (Fin 78)) :
    wordA fE6 l (Pi.single (77 : Fin 78) 1) = vecC 78 (wordS e6T 78 (l.map Fin.val) [(77, 1)]) := by
  rw [single_eq_vecC]
  exact wordA_vecC l _ (by simp)

theorem map_ofNat_val (l : List ℕ) (hl : l.all (fun x => decide (x < 78)) = true) :
    (l.map (Fin.ofNat 78)).map Fin.val = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have := List.all_eq_true.mp hl x hx
  simp only [decide_eq_true_eq] at this
  simp [Fin.ofNat, Nat.mod_eq_of_lt this]

theorem word_mem (l : List ℕ) (hl : l.all (fun x => decide (x < 78)) = true) (hlen : l.length ≤ 3) :
    vecC 78 (wordS e6T 78 l [(77, 1)]) ∈ slotWords fE6 77 3 := by
  have h := wordA_single (l.map (Fin.ofNat 78))
  rw [map_ofNat_val l hl] at h
  rw [← h]
  exact Submodule.subset_span ⟨_, by simpa using hlen, rfl⟩

theorem mem_of_word (l : List ℕ) (hl : l.all (fun x => decide (x < 78)) = true ∧ l.length ≤ 3)
    {c : Fin 78} (lam : ℤ) (hlam : lam ≠ 0)
    (h : zeroL (wordS e6T 78 l [(77, 1)] ++ scale (-lam) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 := by
  have hw := word_mem l hl.1 hl.2
  rw [vecC_eq_of_zeroL lam h, ← single_eq_vecC] at hw
  have := Submodule.smul_mem _ ((lam : ℂ)⁻¹) hw
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam), one_smul] at this

theorem combo_mem (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 78)) && decide (w.1.length ≤ 3)) = true) :
    vecC 78 (ws.flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)]))) ∈ slotWords fE6 77 3 := by
  induction ws with
  | nil =>
    have : vecC 78 ([] : List (ℕ × ℤ)) = 0 := by funext k; simp [vecC, coef]
    simp only [List.flatMap_nil, this]
    exact Submodule.zero_mem _
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hws
    rw [List.flatMap_cons, vecC_append, vecC_scale]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (word_mem w.1 hws.1.1 hws.1.2)) (ih hws.2)

theorem mem_of_combo (ws : List (List ℕ × ℤ))
    (hws : ws.all (fun w => w.1.all (fun x => decide (x < 78)) && decide (w.1.length ≤ 3)) = true)
    {c : Fin 78} (D : ℤ) (hD : D ≠ 0)
    (h : zeroL (ws.flatMap (fun w => scale w.2 (wordS e6T 78 w.1 [(77, 1)])) ++
      scale (-D) [((c : ℕ), 1)]) = true) :
    (Pi.single c 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 := by
  have hsum := combo_mem ws hws
  rw [vecC_eq_of_zeroL D h, ← single_eq_vecC] at hsum
  have := Submodule.smul_mem _ ((D : ℂ)⁻¹) hsum
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hD), one_smul] at this


end

end VOA.DeligneAudit.DeligneCarrier.E6
