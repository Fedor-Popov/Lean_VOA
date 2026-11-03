/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangSectorSugawaraBridge

/-!
# Full Lee--Yang Fock-space primary Ward identity

The heterotypic normal-order telescope and shifted-current Sugawara bridge close the three
remaining modes `m = -2, 1, 2`.  The finite Ward closure theorem then supplies every Virasoro mode and
the exact `K85VirasoroScreeningFieldData` endpoint on the nonintegral Fock carriers.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangFullFockWard

open Module (End)
open ScreeningLowering LeeYangWardClosure
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFockWard
open LeeYangSugawaraReduction LeeYangHeterotypicLocality LeeYangSectorSugawaraBridge
open LatExp

noncomputable section

/-- Scaling the unscaled current-normal-product bracket by `1/4` is exactly the heterotypic
momentum-sector Sugawara bracket. -/
theorem quarter_currentNprodEECBracket (c : ℂ) (a s : ℤ) :
    (1 / 4 : ℂ) • currentNprodEECBracket c a s =
      sectorSugawara c (-a - 2) * EEC c s -
        EEC c s * sectorSugawara 0 (-a - 2) := by
  rw [currentNprodEECBracket, smul_sub,
    ← smul_mul_assoc, ← mul_smul_comm,
    quarter_nprod_sectorCurrentDist, quarter_nprod_sectorCurrentDist]

/-- The momentum-sector Sugawara brackets at consecutive modes differ by the double contraction
`c² E`. -/
theorem sectorSugawaraEEC_firstDifference (c : ℂ) (m s : ℤ) :
    (sectorSugawara c (m + 1) * EEC c s - EEC c s * sectorSugawara 0 (m + 1)) -
        (sectorSugawara c m * EEC c (s - 1) - EEC c (s - 1) * sectorSugawara 0 m) =
      c ^ 2 • EEC c (s - m - 1) := by
  have h := congrArg (fun T : End ℂ LeeYangFock => (1 / 4 : ℂ) • T)
    (currentNprodEECBracket_firstDifference c (-m - 2) s)
  simp only [smul_sub] at h
  rw [quarter_currentNprodEECBracket, quarter_currentNprodEECBracket,
    smul_smul] at h
  rw [show -(-m - 2 - 1) - 2 = m + 1 by ring,
    show -(-m - 2) - 2 = m by ring,
    show s + (-m - 2) + 1 = s - m - 1 by ring] at h
  calc
    _ = (1 / 4 * (2 * c)) • (2 * c) • EEC c (s - m - 1) := h
    _ = c ^ 2 • EEC c (s - m - 1) := by
      rw [smul_smul]
      congr 1
      ring

/-- The sector-Sugawara Ward formula, before the background-charge term. -/
def SectorSugawaraWardAt (c : ℂ) (m : ℤ) : Prop :=
  ∀ s : ℤ,
    sectorSugawara c m * EEC c s - EEC c s * sectorSugawara 0 m =
      (((s - m : ℤ) : ℂ) + ((m + 1 : ℤ) : ℂ) * c ^ 2) • EEC c (s - m)

theorem sectorSugawaraWard_negOne :
    SectorSugawaraWardAt k85FockCharge (-1) := by
  intro s
  have h := sectorSugawara_EEC_of_sugawara k85FockCharge (-1)
    sugawaraEECWardAt_negOne s
  simpa only [Module.End.mul_eq_comp] using h

theorem sectorSugawaraWard_zero :
    SectorSugawaraWardAt k85FockCharge 0 := by
  intro s
  have h := sectorSugawara_EEC_of_sugawara k85FockCharge 0
    sugawaraEECWardAt_zero s
  simpa only [Module.End.mul_eq_comp] using h

/-- The `m=-2` sector-Sugawara Ward identity. -/
theorem sectorSugawaraWard_negTwo :
    SectorSugawaraWardAt k85FockCharge (-2) := by
  intro s
  have hrec := sectorSugawaraEEC_firstDifference k85FockCharge (-2) (s + 1)
  have hbase := sectorSugawaraWard_negOne (s + 1)
  rw [show (-2 : ℤ) + 1 = -1 by norm_num,
    show s + 1 - 1 = s by ring,
    show s + 1 - (-2) - 1 = s + 2 by ring] at hrec
  rw [hbase] at hrec
  rw [show s + 1 - (-1) = s + 2 by ring] at hrec
  rw [show s - (-2) = s + 2 by ring]
  norm_num at hrec ⊢
  push_cast at hrec ⊢
  change
    sectorSugawara k85FockCharge (-2) * EEC k85FockCharge s -
        EEC k85FockCharge s * sectorSugawara 0 (-2) =
      ((s : ℂ) + 2 - k85FockCharge ^ 2) • EEC k85FockCharge (s + 2)
  calc
    _ = ((s : ℂ) + 2) • EEC k85FockCharge (s + 2) -
        k85FockCharge ^ 2 • EEC k85FockCharge (s + 2) := by
      apply (eq_sub_iff_add_eq).2
      exact ((sub_eq_iff_eq_add').1 hrec).symm
    _ = _ := (sub_smul ((s : ℂ) + 2) (k85FockCharge ^ 2)
      (EEC k85FockCharge (s + 2))).symm

/-- The `m=1` sector-Sugawara Ward identity. -/
theorem sectorSugawaraWard_one :
    SectorSugawaraWardAt k85FockCharge 1 := by
  intro s
  have hrec := sectorSugawaraEEC_firstDifference k85FockCharge 0 s
  have hbase := sectorSugawaraWard_zero (s - 1)
  simp only [zero_add, sub_zero] at hrec
  rw [hbase] at hrec
  simp only [sub_zero] at hbase hrec
  rw [show s - 1 = s - 1 by rfl]
  norm_num at hrec ⊢
  push_cast at hrec ⊢
  change
    sectorSugawara k85FockCharge 1 * EEC k85FockCharge s -
        EEC k85FockCharge s * sectorSugawara 0 1 =
      ((s : ℂ) - 1 + 2 * k85FockCharge ^ 2) • EEC k85FockCharge (s - 1)
  calc
    _ = ((s : ℂ) - 1 + k85FockCharge ^ 2) • EEC k85FockCharge (s - 1) +
        k85FockCharge ^ 2 • EEC k85FockCharge (s - 1) :=
      (sub_eq_iff_eq_add').1 hrec
    _ = _ := by
      rw [← add_smul]
      congr 1
      ring

/-- The `m=2` sector-Sugawara Ward identity. -/
theorem sectorSugawaraWard_two :
    SectorSugawaraWardAt k85FockCharge 2 := by
  intro s
  have hrec := sectorSugawaraEEC_firstDifference k85FockCharge 1 s
  have hbase := sectorSugawaraWard_one (s - 1)
  rw [show (1 : ℤ) + 1 = 2 by norm_num, hbase] at hrec
  rw [show s - 1 - 1 = s - 2 by ring] at hrec
  rw [show s - 2 = s - 2 by rfl]
  norm_num at hrec ⊢
  push_cast at hrec ⊢
  change
    sectorSugawara k85FockCharge 2 * EEC k85FockCharge s -
        EEC k85FockCharge s * sectorSugawara 0 2 =
      ((s : ℂ) - 2 + 3 * k85FockCharge ^ 2) • EEC k85FockCharge (s - 2)
  calc
    _ = ((s : ℂ) - 2 + 2 * k85FockCharge ^ 2) • EEC k85FockCharge (s - 2) +
        k85FockCharge ^ 2 • EEC k85FockCharge (s - 2) :=
      (sub_eq_iff_eq_add').1 hrec
    _ = _ := by
      rw [← add_smul]
      congr 1
      ring

/-- Conversely to the reduction theorem, the momentum-sector Sugawara Ward formula recovers the
exact unshifted oscillator identity `SugawaraEECWardAt`. -/
theorem sugawaraEECWardAt_of_sector (c : ℂ) (m : ℤ)
    (h : SectorSugawaraWardAt c m) : SugawaraEECWardAt c m := by
  intro s
  have hs := h s
  rw [sectorSugawara, sectorSugawara] at hs
  by_cases hm : m = 0
  · subst m
    simp only [alphaMode, HeisenbergN.oscN_zero, smul_zero, zero_smul, zero_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sub_zero,
      if_pos (rfl : (0 : ℤ) = 0), if_true, Int.cast_zero, Int.cast_one,
      zero_add, one_mul] at hs ⊢
    rw [show
        (HeisenbergN.LvirN 1 2 0 + c ^ 2 • 1) * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 0 =
          (HeisenbergN.LvirN 1 2 0 * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 0) + c ^ 2 • EEC c s by
          simp only [add_mul, smul_mul_assoc, one_mul]
          abel] at hs
    push_cast at hs ⊢
    exact eq_sub_of_add_eq hs
  · simp only [if_neg hm, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_smul, add_zero, sub_zero] at hs ⊢
    rw [show
        (HeisenbergN.LvirN 1 2 m + c • alphaMode m) * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 m =
          (HeisenbergN.LvirN 1 2 m * EEC c s -
            EEC c s * HeisenbergN.LvirN 1 2 m) +
            c • (alphaMode m * EEC c s) by
          simp only [add_mul, smul_mul_assoc]
          abel] at hs
    push_cast at hs ⊢
    exact eq_sub_of_add_eq hs

theorem sugawaraEECWardAt_negTwo :
    SugawaraEECWardAt k85FockCharge (-2) :=
  sugawaraEECWardAt_of_sector k85FockCharge (-2) sectorSugawaraWard_negTwo

theorem sugawaraEECWardAt_one :
    SugawaraEECWardAt k85FockCharge 1 :=
  sugawaraEECWardAt_of_sector k85FockCharge 1 sectorSugawaraWard_one

theorem sugawaraEECWardAt_two :
    SugawaraEECWardAt k85FockCharge 2 :=
  sugawaraEECWardAt_of_sector k85FockCharge 2 sectorSugawaraWard_two

theorem k85FockField_primaryWard_negTwo :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField (-2) :=
  k85FockField_primaryWard_of_sugawara (-2) sugawaraEECWardAt_negTwo

theorem k85FockField_primaryWard_one :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField 1 :=
  k85FockField_primaryWard_of_sugawara 1 sugawaraEECWardAt_one

theorem k85FockField_primaryWard_two :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField 2 :=
  k85FockField_primaryWard_of_sugawara 2 sugawaraEECWardAt_two

/-- The full half-power primary Ward identity on the nonintegral Lee--Yang Fock sectors. -/
theorem k85FockField_primaryWard_all (m : ℤ) :
    PrimaryWardAt k85ScreeningVirWeight k85SourceL k85TargetL k85FockField m :=
  primaryWard_all_of_five k85ScreeningVirWeight k85SourceL k85TargetL k85FockField
    k85SourceL_isLeeYang k85TargetL_isLeeYang
    k85FockField_primaryWard_negTwo k85FockField_primaryWard_negOne
    k85FockField_primaryWard_zero k85FockField_primaryWard_one
    k85FockField_primaryWard_two m

/-- Exact Fock-space realization of the Virasoro screening-field interface consumed by inverse
DS.  Quotient descent is deliberately a separate theorem. -/
noncomputable def k85FockVirasoroScreeningFieldData :
    K85VirasoroScreeningFieldData (Vir := LeeYangFock) (ShiftedVir := LeeYangFock) where
  sourceL := k85SourceL
  targetL := k85TargetL
  field := k85FockField
  isHeterotypicField := k85FockField_isHeterotypicField
  ward := by
    intro m t
    exact k85FockField_primaryWard_all m t

end
end LeeYangFullFockWard
end InverseDS
end VOA
