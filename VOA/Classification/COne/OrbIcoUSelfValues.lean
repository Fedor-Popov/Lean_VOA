import VOA.Classification.COne.OrbIcoSCriteria

/-! Arithmetic of the candidate self-channel measurements computed externally.
These identities do not identify the numbers with measurements of VOA products. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbIcoU
open OrbXu

def self38Numerator : ℚ :=
  -260952337207748553581264188127412319344 / 18011693843864699803625515

def self38Denominator : ℚ := -24503092456880799496960016608613671875 / 8

def self40Numerator : ℚ :=
  -23821248793955097464450262497352583440000 / 148967303202786870140573377

def self40Denominator : ℚ := -1199884719527911127571619589973720703125

def self38Ratio : ℚ := self38Numerator / self38Denominator
def self40Ratio : ℚ := self40Numerator / self40Denominator

theorem self38_ratio : self38Ratio = xuV19 := by
  norm_num [self38Ratio, self38Numerator, self38Denominator, xuV19]

theorem self40_ratio : self40Ratio = xuV20 := by
  norm_num [self40Ratio, self40Numerator, self40Denominator, xuV20]

theorem self_ratios_compatible : self38Ratio * xuV20 = self40Ratio * xuV19 := by
  rw [self38_ratio, self40_ratio, mul_comm]

theorem self38Ratio_ne_zero : self38Ratio ≠ 0 := by
  norm_num [self38Ratio, self38Numerator, self38Denominator]

theorem self40Ratio_ne_zero : self40Ratio ≠ 0 := by
  norm_num [self40Ratio, self40Numerator, self40Denominator]

end VOA.Classification.COne.OrbIcoU
