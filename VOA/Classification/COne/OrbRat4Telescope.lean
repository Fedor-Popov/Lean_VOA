import VOA.Classification.COne.OrbRat3Telescope
import VOA.Classification.COne.OrbRat4N0
import VOA.Classification.COne.OrbRat4N1
import VOA.Classification.COne.OrbRat4N2
import VOA.Classification.COne.OrbRat4N3
import VOA.Classification.COne.OrbRat4N4

/-! # The vacuum telescope of the tetrahedral model, unconditionally

`OrbRat3.telescope_V8` is conditional on `V8OuterCertificates` (five list identities about the
evaluator `actU`, whose kernel check exceeded the memory budget).  The outer products
`U₍₁₆₋ₙ₎ U₍ₙ₎ h(-1)1`, `n ≤ 4`, are proved directly (`OrbRat4N0`–`OrbRat4N4`), through
skew-symmetry (`OrbRat4Skew`) and monomial-wise kernel certificates.  So

* `telescope_V8_holds`: `∑_{n<9} (-1)ⁿ C(16,n) U₍₁₆₋ₙ₎ U₍ₙ₎ h = -345600 h` in `V₈`, with no
  hypothesis;
* the `OrbRat3` consequences hold without the hypothesis `V8OuterCertificates`.

`V8OuterCertificates` itself (the literal list identities) is not proved here; it is not
needed by any consequence.
-/
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat4

open VOA VertexOperatorAlgebra PlusSplitting PlusRational OrbRat2 OrbC2e OrbRat3

/-- The `V₈` telescope of the weight-nine generator on `h(-1)1`, unconditionally. -/
theorem telescope_V8_holds :
    ∑ n ∈ Finset.range 9, ((-1 : ℂ) ^ n * ((16 : ℕ).choose n : ℂ)) •
      (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - n) ((V2m 4 four_ge_one).smul Uc n hV) =
        (-345600 : ℂ) • hV := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e6 : (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - ((6 : ℕ) : ℤ))
      ((V2m 4 four_ge_one).smul Uc ((6 : ℕ) : ℤ) hV) = 0 := by
    rw [show (((6 : ℕ) : ℤ)) = 6 by rfl, inner_6]; exact smul_evalSt_empty _
  have e7 : (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - ((7 : ℕ) : ℤ))
      ((V2m 4 four_ge_one).smul Uc ((7 : ℕ) : ℤ) hV) = 0 := by
    rw [show (((7 : ℕ) : ℤ)) = 7 by rfl, inner_7]; exact smul_evalSt_empty _
  have e8 : (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - ((8 : ℕ) : ℤ))
      ((V2m 4 four_ge_one).smul Uc ((8 : ℕ) : ℤ) hV) = 0 := by
    rw [show (((8 : ℕ) : ℤ)) = 8 by rfl, inner_8]; exact smul_evalSt_empty _
  rw [e6, e7, e8]
  have o0 := outer0
  have o1 := outer1
  have o2 := outer2
  have o3 := outer3
  have o4 := outer4
  have o5 := outer_5
  norm_num only at o0 o1 o2 o3 o4 o5 ⊢
  rw [o0, o1, o2, o3, o4, o5]
  simp only [smul_smul, ← add_smul]
  norm_num [Nat.choose]

/-- `CubicVacuumTelescope` from `C₂` and the two Zhu inputs (no evaluator hypothesis). -/
theorem cubicVacuumTelescope_of_zhu (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable) : CubicVacuumTelescope :=
  cubicVacuumTelescope_of_V8 hC2 hdim htab telescope_value_ne_zero telescope_V8_holds

/-- The resonant pair `(1 ↘ 0)` of the tetrahedral model splits from `C₂` and the Zhu inputs. -/
theorem cubic_pair_one_zero_of_zhu (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable) :
    PlusRat2Dual.PairSplit cubicModel 1 0 :=
  cubic_pair_one_zero hC2 hdim htab (cubicVacuumTelescope_of_zhu hC2 hdim htab)

/-- Rationality of the tetrahedral model from `C₂`, the two Zhu inputs, and the two
non-vacuum resonant pairs. -/
theorem cubicModel_admissiblyRational_of_zhu (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable)
    (hnv : CubicNonVacuumPairs) : AdmissiblyRational cubicModel :=
  cubicModel_admissiblyRational_of_reduced hC2 hdim htab
    (cubicVacuumTelescope_of_zhu hC2 hdim htab) hnv

theorem cubicModelRationalOfC2_of_zhu (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (hnv : CubicNonVacuumPairs) : CubicModelRationalOfC2 :=
  fun hC2 => cubicModel_admissiblyRational_of_zhu hC2 hdim htab hnv

end VOA.Classification.COne.OrbRat4
