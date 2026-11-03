import VOA.Classification.COne.OrbC2gArithmetic
import VOA.Classification.COne.OrbC2gProbe

/-! # The exact remaining finite check for the coefficient discrepancy

These two Props are arithmetic certificates, not the requested Virasoro
remainder memberships. Their state-level consequences are proved. Neither
certificate is asserted as a theorem here.
-/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2g
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2b OrbC2e OrbC2f

/-- OPEN finite arithmetic check for the normalized weight-20 self-product. -/
def WeightTwentyLeadingCertificate : Prop :=
  leadPoly (zeroSector (selfVector (-3) 16)) = [(printedLeading 20, [])]

/-- OPEN finite arithmetic check for the normalized weight-22 self-product. -/
def WeightTwentyTwoLeadingCertificate : Prop :=
  leadPoly (zeroSector (selfVector (-5) 18)) = [(printedLeading 22, [])]

/-- This exact finite check would establish the discrepancy on actual VOA states. -/
theorem weight_twenty_probe_of_certificate (h : WeightTwentyLeadingCertificate) :
    neutralProbe ((V2mPlus 4 four_ge_one).smul normalizedNine (-3) normalizedNine :
      LatModuleGen (latP 4)) = (djC20 : ℂ) / 13 := by
  rw [normalizedNine_neg_three_vector, neutralProbe_of_certificate _ _ h,
    printedLeading_twenty_eq_thirteenth]
  push_cast
  rfl

/-- At weight 22 the corresponding finite check would confirm the existing constant. -/
theorem weight_twenty_two_probe_of_certificate (h : WeightTwentyTwoLeadingCertificate) :
    neutralProbe ((V2mPlus 4 four_ge_one).smul normalizedNine (-5) normalizedNine :
      LatModuleGen (latP 4)) = (djC22 : ℂ) := by
  rw [normalizedNine_neg_five_vector, neutralProbe_of_certificate _ _ h,
    printedLeading_twenty_two]

/-- The conditional mismatch is specifically a probe identity, not a
claimed negation of the existential `CubicSeedRemainders`. -/
theorem weight_twenty_probe_ne_target_of_certificate (h : WeightTwentyLeadingCertificate) :
    neutralProbe ((V2mPlus 4 four_ge_one).smul normalizedNine (-3) normalizedNine :
      LatModuleGen (latP 4)) ≠ (djC20 : ℂ) := by
  rw [weight_twenty_probe_of_certificate h]
  norm_num [djC20]

end VOA.Classification.COne.OrbC2g
