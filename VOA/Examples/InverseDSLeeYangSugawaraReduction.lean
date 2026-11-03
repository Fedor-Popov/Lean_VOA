/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangFockWard

/-!
# Reduction of the Lee--Yang Fock Ward identity to the oscillator Sugawara bracket

The nonintegral momentum and the background charge introduce no further analytic difficulty.
This file isolates the exact remaining free-boson identity.  An unshifted Sugawara bracket for
`EEC c` immediately gives the heterotypic Feigin--Fuchs Ward identity between momentum sectors
`0` and `c`; at the selected Lee--Yang parameters it gives `PrimaryWardAt` for the half-power
field.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangSugawaraReduction

open Module (End)
open ScreeningLowering LeeYangWardClosure
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFockWard
open LatExp

noncomputable section

/-- The exact unshifted rank-one Sugawara/exponential identity.  The exceptional zero-mode
term compensates for the fact that the polynomial oscillator carrier has `alphaMode 0 = 0`;
the missing momentum zero mode is restored by `sectorSugawara`. -/
def SugawaraEECWardAt (c : ℂ) (m : ℤ) : Prop :=
  ∀ s : ℤ,
    HeisenbergN.LvirN 1 2 m * EEC c s - EEC c s * HeisenbergN.LvirN 1 2 m =
      (((s - m : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) * c ^ 2) • EEC c (s - m)
        - c • (alphaMode m * EEC c s)
        - (if m = 0 then c ^ 2 • EEC c s else 0)

/-- The oscillator Sugawara identity gives the momentum-sector Sugawara Ward identity. -/
theorem sectorSugawara_EEC_of_sugawara (c : ℂ) (m : ℤ)
    (h : SugawaraEECWardAt c m) (s : ℤ) :
    (sectorSugawara c m).comp (EEC c s) -
        (EEC c s).comp (sectorSugawara 0 m) =
      (((s - m : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) * c ^ 2) •
        EEC c (s - m) := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  rw [sectorSugawara, sectorSugawara]
  have hs := h s
  by_cases hm : m = 0
  · subst m
    simp only [if_pos True.intro, alphaMode, HeisenbergN.oscN_zero, zero_smul,
      smul_zero, zero_mul, add_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hs ⊢
    rw [show
        (HeisenbergN.LvirN 1 2 0 + c ^ 2 • 1) * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 0 =
          (HeisenbergN.LvirN 1 2 0 * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 0) + c ^ 2 • EEC c s by
          simp only [add_mul, smul_mul_assoc, one_mul]
          abel,
      hs]
    module
  · simp only [if_neg hm, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_smul, add_zero] at hs ⊢
    rw [show
        (HeisenbergN.LvirN 1 2 m + c • alphaMode m) * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 m =
          (HeisenbergN.LvirN 1 2 m * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 m) +
            c • (alphaMode m * EEC c s) by
          simp only [add_mul, smul_mul_assoc]
          abel,
      hs]
    abel

/-- After the momentum-sector Sugawara identity, the background term contributes only the
current contraction `-2 ell c (m+1)`. -/
theorem sectorVirasoro_EEC_of_sugawara
    (c ell : ℂ) (m : ℤ) (h : SugawaraEECWardAt c m) (s : ℤ) :
    (sectorVirasoro ell c m).comp (EEC c s) -
        (EEC c s).comp (sectorVirasoro ell 0 m) =
      (((s - m : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) *
        (c ^ 2 - 2 * ell * c)) • EEC c (s - m) := by
  rw [sectorVirasoro, sectorVirasoro, sectorBackgroundCurrent,
    sectorBackgroundCurrent]
  have hSug := sectorSugawara_EEC_of_sugawara c m h s
  have hCur := sectorCurrent_heterotypic_EEC c m s
  rw [show
      (sectorSugawara c m - (((m : ℂ) + 1) • ell • sectorCurrent c m)).comp
            (EEC c s) -
          (EEC c s).comp
            (sectorSugawara 0 m - (((m : ℂ) + 1) • ell • sectorCurrent 0 m)) =
        ((sectorSugawara c m).comp (EEC c s) -
          (EEC c s).comp (sectorSugawara 0 m)) -
          (((m : ℂ) + 1) * ell) •
            ((sectorCurrent c m).comp (EEC c s) -
              (EEC c s).comp (sectorCurrent 0 m)) by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          map_sub, map_smul]
        module,
    hSug, hCur, smul_smul]
  push_cast
  module

/-- At the selected Lee--Yang momentum/background, the oscillator identity at `m` gives the
integer-indexed EEC primary Ward identity at `m`. -/
theorem k85EEC_primaryWard_of_sugawara (m : ℤ)
    (h : SugawaraEECWardAt k85FockCharge m) (s : ℤ) :
    (k85TargetL m).comp (EEC k85FockCharge s) -
        (EEC k85FockCharge s).comp (k85SourceL m) =
      (((s - m : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) *
        k85ScreeningVirWeight) • EEC k85FockCharge (s - m) := by
  rw [k85TargetL, k85SourceL]
  rw [sectorVirasoro_EEC_of_sugawara k85FockCharge k85FockBackground m h s,
    k85FockWeight]

/-- Reindexing an integer-index EEC Ward identity gives the exact half-power Ward interface at
the same Virasoro mode. -/
theorem k85FockField_primaryWard_of_sugawara (m : ℤ)
    (h : SugawaraEECWardAt k85FockCharge m) :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField m := by
  intro t
  by_cases ht : EvenHalfPowerMatch t
  · obtain ⟨s, hs⟩ := ht
    have hshift : t - 2 * m = 2 * (s - m) := by omega
    rw [k85FockField_of_eq t s hs,
      k85FockField_of_eq (t - 2 * m) (s - m) hshift,
      homBracket, k85EEC_primaryWard_of_sugawara m h s]
    congr 1
    rw [hs]
    push_cast
    ring
  · have htshift : ¬ EvenHalfPowerMatch (t - 2 * m) := by
      rintro ⟨s, hs⟩
      exact ht ⟨s + m, by omega⟩
    rw [k85FockField_of_not_match t ht,
      k85FockField_of_not_match (t - 2 * m) htshift]
    simp [homBracket]

/-- The existing translation calculation supplies the unshifted oscillator identity at `-1`. -/
theorem sugawaraEECWardAt_negOne : SugawaraEECWardAt k85FockCharge (-1) := by
  intro s
  have h := LatExp.LvirN_comm_EEC k85FockCharge s
  change HeisenbergN.LvirN 1 2 (-1) * EEC k85FockCharge s -
    EEC k85FockCharge s * HeisenbergN.LvirN 1 2 (-1) = _ at h
  rw [← Int.cast_smul_eq_zsmul ℂ (s + 1)] at h
  push_cast at h
  simp only [sub_neg_eq_add, Int.cast_add, Int.cast_one, Int.cast_negSucc,
    neg_add_cancel, Int.cast_zero, zero_mul, add_zero, zero_smul, sub_zero,
    if_neg (by norm_num : (-1 : ℤ) ≠ 0)]
  simpa only [alphaMode] using h

/-- The existing grading calculation supplies the unshifted oscillator identity at `0`. -/
theorem sugawaraEECWardAt_zero : SugawaraEECWardAt k85FockCharge 0 := by
  intro s
  simp only [sub_zero, Int.cast_zero, Int.cast_one, zero_add, one_mul,
    alphaMode, HeisenbergN.oscN_zero, zero_mul, smul_zero,
    if_pos True.intro, sub_zero]
  rw [Lzero_comm_EEC]
  module

end
end LeeYangSugawaraReduction
end InverseDS
end VOA
