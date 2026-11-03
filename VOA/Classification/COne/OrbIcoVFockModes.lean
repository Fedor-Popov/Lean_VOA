import VOA.Examples.VirasoroVermaBSAAllLevels
import VOA.Examples.VirasoroFockGramTransfer

/-! Negative modes in the first-row Fock family used for the icosahedral symbols. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial InverseDS.VirasoroVerma
  InverseDS.LeeYangFockVirasoro

abbrev FF := FockN 1

def familyBackground (s : ℂ) : ℂ := (s - s⁻¹) / 2

def familyMomentum (s : ℂ) : ℂ := 6 / s

def familyVariable (s : ℂ) (n : ℕ) : FF := s • X (n, (0 : Fin 1))

/-- The actual central charge equals the first-row BSA charge. -/
theorem family_charge (s : ℂ) (hs : s ≠ 0) :
    1 - 24 * familyBackground s ^ 2 = vermaBSACharge (s ^ 2) := by
  unfold familyBackground vermaBSACharge
  field_simp
  ring

/-- The actual momentum vacuum has the desired first-row highest weight. -/
theorem family_weight (s : ℂ) (hs : s ≠ 0) :
    familyMomentum s ^ 2 - 2 * familyBackground s * familyMomentum s =
      vermaBSAWeight 13 (s ^ 2) := by
  unfold familyBackground familyMomentum vermaBSAWeight
  field_simp
  ring

private theorem sugTerm_vacuum_support (k : ℕ) (j : ℤ)
    (hj : sugTermN 1 2 0 (-(k : ℤ)) j (vacuumN 1) ≠ 0) :
    -(k : ℤ) < j ∧ j < 0 := by
  rw [sugTermN_apply] at hj
  by_cases hneg : j < 0
  · rw [if_pos hneg] at hj
    refine ⟨?_, hneg⟩
    by_contra hbad
    have hge : 0 ≤ -(k : ℤ) - j := by omega
    rw [oscN_vacuum 1 2 0 _ hge, map_zero] at hj
    exact hj rfl
  · rw [if_neg hneg, oscN_vacuum 1 2 0 j (by omega), map_zero] at hj
    exact (hj rfl).elim

private theorem sugTerm_vacuum_window (k i : ℕ) (hi : i < k - 1) :
    sugTermN 1 2 0 (-(k : ℤ)) (-((i : ℤ) + 1)) (vacuumN 1) =
      X (i, (0 : Fin 1)) * X (k - 2 - i, (0 : Fin 1)) := by
  rw [sugTermN_apply, if_pos (by omega),
    oscN_apply_neg 1 2 0 (by omega), oscN_apply_neg 1 2 0 (by omega)]
  have h1 : (-(-((i : ℤ) + 1)) - 1).toNat = i := by omega
  have h2 : (-(-(k : ℤ) - -((i : ℤ) + 1)) - 1).toNat = k - 2 - i := by omega
  rw [h1, h2]
  simp [vacuumN]

theorem LvirN_negative_vacuum (k : ℕ) (hk : 0 < k) :
    LvirN 1 2 (-(k : ℤ)) (vacuumN 1) = (1 / 4 : ℂ) •
      ∑ i ∈ Finset.range (k - 1), X (i, (0 : Fin 1)) * X (k - 2 - i, (0 : Fin 1)) := by
  classical
  let emb : ℕ ↪ ℤ := ⟨fun i => -((i : ℤ) + 1), by
    intro a b h
    change -((a : ℤ) + 1) = -((b : ℤ) + 1) at h
    omega⟩
  have hsup : Function.support (fun j : ℤ =>
      sugTermN 1 2 0 (-(k : ℤ)) j (vacuumN 1)) ⊆ (Finset.range (k - 1)).map emb := by
    intro j hj
    have hh := sugTerm_vacuum_support k j (Function.mem_support.mp hj)
    change j ∈ (Finset.range (k - 1)).map emb
    rw [Finset.mem_map]
    refine ⟨(-j - 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · change -((((-j - 1).toNat : ℕ) : ℤ) + 1) = j
      omega
  rw [LvirN_apply, Fintype.sum_unique, LvirNa_apply']
  change (1 / (2 * 2) : ℂ) • ∑ᶠ j : ℤ, sugTermN 1 2 0 (-(k : ℤ)) j (vacuumN 1) = _
  rw [finsum_eq_finsetSum_of_support_subset _ hsup, Finset.sum_map]
  norm_num only [show (1 / (2 * 2) : ℂ) = 1 / 4 by norm_num]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact sugTerm_vacuum_window k i (Finset.mem_range.mp hi)

/-- Negative charged-background modes have a finite creation vacuum polynomial. -/
theorem sector_negative_vacuum (ell p : ℂ) (k : ℕ) (hk : 0 < k) :
    sectorVirasoro ell p (-(k : ℤ)) (vacuumN 1) =
      (1 / 4 : ℂ) • (∑ i ∈ Finset.range (k - 1),
        X (i, (0 : Fin 1)) * X (k - 2 - i, (0 : Fin 1))) +
      (p + ((k : ℂ) - 1) * ell) • X (k - 1, (0 : Fin 1)) := by
  rw [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    if_neg (show -(k : ℤ) ≠ 0 by omega)]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    if_neg (show -(k : ℤ) ≠ 0 by omega), zero_smul, add_zero, alphaMode]
  rw [LvirN_negative_vacuum k hk, oscN_apply_neg 1 2 0 (by omega)]
  have he : (-(-(k : ℤ)) - 1).toNat = k - 1 := by omega
  rw [he]
  simp only [vacuumN, mul_one, Int.cast_neg, Int.cast_natCast, smul_smul]
  module

/-- Commuting through a creation variable leaves the standard derivative term. -/
theorem sector_negative_X (ell p : ℂ) (k : ℕ) (hk : 0 < k) (i : ℕ) (P : FF) :
    sectorVirasoro ell p (-(k : ℤ)) (X (i, (0 : Fin 1)) * P) =
      X (i, (0 : Fin 1)) * sectorVirasoro ell p (-(k : ℤ)) P +
        ((i + 1 : ℕ) : ℂ) • (X (i + k, (0 : Fin 1)) * P) := by
  have hL := LvirN_oscN 1 2 (by norm_num) (0 : Fin 1)
    (-(k : ℤ)) (-((i : ℤ) + 1)) P
  rw [oscN_apply_neg 1 2 0 (by omega), oscN_apply_neg 1 2 0 (by omega),
    oscN_apply_neg 1 2 0 (by omega)] at hL
  have h1 : (-(-((i : ℤ) + 1)) - 1).toNat = i := by omega
  have h2 : (-(-(k : ℤ) + -((i : ℤ) + 1)) - 1).toNat = i + k := by omega
  rw [h1, h2] at hL
  have hA : alphaMode (-(k : ℤ)) (X (i, (0 : Fin 1)) * P) =
      X (i, (0 : Fin 1)) * alphaMode (-(k : ℤ)) P := by
    rw [alphaMode, oscN_apply_neg 1 2 0 (by omega), oscN_apply_neg 1 2 0 (by omega)]
    ring
  simp only [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    if_neg (show -(k : ℤ) ≠ 0 by omega), zero_smul, add_zero,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hL, hA]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
    Nat.cast_one, neg_neg]
  simp only [smul_eq_C_mul, map_add, map_mul, map_natCast]
  ring

end VOA.Classification.COne.OrbIcoV
