/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangFockVirasoro
import VOA.Examples.LatticeGeneralLocality
import VOA.Examples.LatticeExpVirasoro
import VOA.Examples.LatticeVOAInstance

/-!
# Ward identities for the nonintegral Lee--Yang Fock exponential

This file begins the concrete Ward calculation.  It first upgrades the existing arbitrary-charge
current/dressing OPE to a heterotypic current identity between the momentum-zero and momentum-`c`
Fock sectors.  It then proves the `L_{-1}` and `L_0` primary Ward identities for the half-power
Lee--Yang field.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangFockWard

open Module (End)
open ScreeningLowering
open LeeYangWardClosure
open LeeYangFockExponential LeeYangFockVirasoro
open LatExp

noncomputable section

/-- Arbitrary-charge oscillator commutator, extracted from
`LatticeGeneralLocality.alphaField_comm_EECc`. -/
theorem alphaMode_comm_EEC (c : ℂ) (m s : ℤ) :
    alphaMode m * EEC c s - EEC c s * alphaMode m =
      (if m = 0 then 0 else (2 * c) • EEC c (s - m)) := by
  have h := LatExp.alphaField_comm_EECc c (-m - 1) s
  rw [bracketDist_apply, LatExp.alphaField_apply] at h
  have hidx : -(-m - 1) - 1 = m := by ring
  rw [hidx] at h
  by_cases hm : m = 0
  · have hj : -m - 1 = -1 := by omega
    simpa only [alphaMode, if_pos hm, if_pos hj] using h
  · have hj : -m - 1 ≠ -1 := by omega
    simpa only [alphaMode, if_neg hm, if_neg hj,
      show s + (-m - 1) + 1 = s - m by ring] using h

/-- The shifted target current minus the source current contracts with the exponential uniformly,
including the momentum-zero mode. -/
theorem sectorCurrent_heterotypic_EEC (c : ℂ) (m s : ℤ) :
    (sectorCurrent c m).comp (EEC c s) -
        (EEC c s).comp (sectorCurrent 0 m) =
      (2 * c) • EEC c (s - m) := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  rw [sectorCurrent, sectorCurrent]
  by_cases hm : m = 0
  · simp only [if_pos hm, mul_zero, zero_smul, add_zero]
    rw [add_mul, smul_mul_assoc, one_mul]
    have hc := alphaMode_comm_EEC c m s
    rw [if_pos hm] at hc
    rw [show alphaMode m * EEC c s + (2 * c) • EEC c s -
        EEC c s * alphaMode m =
      (alphaMode m * EEC c s - EEC c s * alphaMode m) +
        (2 * c) • EEC c s by abel,
      hc, hm, sub_zero]
    module
  · simp only [if_neg hm, zero_smul, add_zero]
    rw [alphaMode_comm_EEC, if_neg hm]

/-- `L_0` acts by the integer grade on every integer-graded Fock vector. -/
theorem Lzero_gradingZN {d : ℤ} {x : LeeYangFock}
    (hx : x ∈ HeisenbergN.gradingZN 1 d) :
    HeisenbergN.LvirN 1 2 0 x = (d : ℂ) • x := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [HeisenbergN.gradingZN_of_neg hd, Submodule.mem_bot] at hx
    rw [hx, map_zero, smul_zero]
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hx
    rw [HeisenbergN.LvirN_zero_gradingWN 1 2 (by norm_num) hx]
    congr 1
    norm_cast
    exact Int.toNat_of_nonneg hd

/-- The oscillator dressing has the expected `L_0` commutator. -/
theorem Lzero_comm_EEC (c : ℂ) (s : ℤ) :
    HeisenbergN.LvirN 1 2 0 * EEC c s -
        EEC c s * HeisenbergN.LvirN 1 2 0 =
      (s : ℂ) • EEC c s := by
  apply LinearMap.ext
  intro x
  obtain ⟨cc, rfl⟩ := (HeisenbergN.gradingWN_isInternal 1).2 x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum,
    LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hin := HeisenbergN.mem_gradingZN_of_gradingWN (cc w).2
  have hout := LatExp.EEC_memZ c s hin
  rw [Lzero_gradingZN hout, HeisenbergN.LvirN_zero_gradingWN 1 2
    (by norm_num) (cc w).2, map_smul]
  push_cast
  module

/-- The oscillator-index Ward identity at `m=-1`. -/
theorem EEC_primaryWard_negOne (s : ℤ) :
    (k85TargetL (-1)).comp (EEC k85FockCharge s) -
        (EEC k85FockCharge s).comp (k85SourceL (-1)) =
      (s + 1 : ℤ) • EEC k85FockCharge (s + 1) := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  simp only [k85TargetL, k85SourceL, sectorVirasoro, sectorSugawara,
    sectorBackgroundCurrent]
  rw [show (((-1 : ℤ) : ℂ) + 1) = 0 by norm_num,
    if_neg (by norm_num : (-1 : ℤ) ≠ 0)]
  simp only [if_neg (by norm_num : (-1 : ℤ) ≠ 0)]
  simp only [zero_smul, sub_zero, add_zero]
  change
    (HeisenbergN.LvirN 1 2 (-1) + k85FockCharge • alphaMode (-1)) *
        EEC k85FockCharge s -
      EEC k85FockCharge s * HeisenbergN.LvirN 1 2 (-1) = _
  rw [add_mul, smul_mul_assoc]
  have hL := LatExp.LvirN_comm_EEC k85FockCharge s
  change HeisenbergN.LvirN 1 2 (-1) * EEC k85FockCharge s -
      EEC k85FockCharge s * HeisenbergN.LvirN 1 2 (-1) = _ at hL
  rw [show
      HeisenbergN.LvirN 1 2 (-1) * EEC k85FockCharge s +
          k85FockCharge • (alphaMode (-1) * EEC k85FockCharge s) -
          EEC k85FockCharge s * HeisenbergN.LvirN 1 2 (-1) =
        (HeisenbergN.LvirN 1 2 (-1) * EEC k85FockCharge s -
          EEC k85FockCharge s * HeisenbergN.LvirN 1 2 (-1)) +
          k85FockCharge • (alphaMode (-1) * EEC k85FockCharge s) by abel,
    hL]
  change
    ((s + 1 : ℤ) • EEC k85FockCharge (s + 1) -
        k85FockCharge • (alphaMode (-1) * EEC k85FockCharge s)) +
      k85FockCharge • (alphaMode (-1) * EEC k85FockCharge s) = _
  abel

/-- The oscillator-index Ward identity at `m=0`. -/
theorem EEC_primaryWard_zero (s : ℤ) :
    (k85TargetL 0).comp (EEC k85FockCharge s) -
        (EEC k85FockCharge s).comp (k85SourceL 0) =
      ((s : ℂ) + k85ScreeningVirWeight) • EEC k85FockCharge s := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  simp only [k85TargetL, k85SourceL, sectorVirasoro, sectorSugawara,
    sectorBackgroundCurrent, sectorCurrent]
  norm_num [alphaMode, HeisenbergN.oscN_zero]
  rw [show
      (HeisenbergN.LvirN 1 2 0 + k85FockCharge ^ 2 • 1 -
          k85FockBackground • ((2 * k85FockCharge) • 1)) * EEC k85FockCharge s -
        EEC k85FockCharge s * HeisenbergN.LvirN 1 2 0 =
      (HeisenbergN.LvirN 1 2 0 * EEC k85FockCharge s -
        EEC k85FockCharge s * HeisenbergN.LvirN 1 2 0) +
        (k85FockCharge ^ 2 - 2 * k85FockBackground * k85FockCharge) •
          EEC k85FockCharge s by
        simp only [sub_mul, add_mul, smul_mul_assoc, one_mul, smul_smul]
        module,
    Lzero_comm_EEC, k85FockWeight, ← add_smul]

/-- Half-power Ward identity at `L_{-1}`. -/
theorem k85FockField_primaryWard_negOne :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField (-1) := by
  intro t
  simp only [show t - 2 * (-1) = t + 2 by ring, Int.cast_negSucc,
    Int.cast_one, neg_add_cancel, zero_mul, add_zero]
  by_cases hm : EvenHalfPowerMatch t
  · obtain ⟨s, hs⟩ := hm
    rw [k85FockField_of_eq t s hs,
      k85FockField_of_eq (t + 2) (s + 1) (by omega), homBracket,
      EEC_primaryWard_negOne]
    rw [← Int.cast_smul_eq_zsmul ℂ (s + 1)]
    congr 1
    rw [hs]
    push_cast
    ring
  · have hmshift : ¬ EvenHalfPowerMatch (t + 2) := by
      rintro ⟨s, hs⟩
      exact hm ⟨s - 1, by omega⟩
    rw [k85FockField_of_not_match t hm, k85FockField_of_not_match (t + 2) hmshift]
    simp [homBracket]

/-- Half-power Ward identity at `L_0`. -/
theorem k85FockField_primaryWard_zero :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField 0 := by
  intro t
  simp only [show t - 2 * 0 = t by ring, Int.cast_zero, zero_add, one_mul]
  by_cases hm : EvenHalfPowerMatch t
  · obtain ⟨s, hs⟩ := hm
    rw [k85FockField_of_eq t s hs, homBracket, EEC_primaryWard_zero]
    congr 1
    rw [hs]
    push_cast
    ring
  · rw [k85FockField_of_not_match t hm]
    simp [homBracket]

end
end LeeYangFockWard
end InverseDS
end VOA
