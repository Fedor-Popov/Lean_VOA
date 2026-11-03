import VOA.Classification.COne.OrbRat3Module
import VOA.Classification.COne.OrbRat3Residual
import VOA.Classification.COne.OrbRat3Outer5

/-! # The vacuum telescope of the tetrahedral model: `λ = -345600`

`telescope_V8`: in the lattice VOA `V₈`, with `U = J₍₋₂₎E − E₍₋₂₎J` (`OrbC2e.weightNine`, the
weight-nine generator of `(V₈⁺)^{ℤ/3}`) and `h = h(-1)1`,

  `∑_{n<9} (-1)ⁿ C(16,n) U₍₁₆₋ₙ₎ U₍ₙ₎ h = -345600 h`.

Kernel-certified: all inner products `U₍ₙ₎ h` (`OrbRat3Inner`) and the outer product for
`n = 5` (`OrbRat3Outer5`); `n ≥ 6` vanish.  The outer products for
`n = 0,…,4` are the explicit decidable hypothesis `V8OuterCertificates` (`OrbRat3Residual`):
the kernel check exceeded the memory budget.  So every theorem below is CONDITIONAL on
`V8OuterCertificates`.

Consequences:
* `cubicVacuumTelescope_of_zhu : V8OuterCertificates → C2Cofinite cubicModel →
  CubicZhuDimensionBound →
  CubicZhuCharacterTable → CubicVacuumTelescope`.  The telescope input of `OrbRat2Vacuum` is no
  longer an independent hypothesis.
* `cubic_pair_one_zero_of_zhu`: the resonant pair `(1 ↘ 0)` splits from the Zhu inputs alone.
* `cubicModel_admissiblyRational_of_zhu`: rationality of the tetrahedral model from `C₂`, the two
  Zhu inputs, and `CubicNonVacuumPairs`.
-/
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat3

open VOA VertexOperatorAlgebra PlusSplitting PlusRational OrbRat2 OrbC2e

theorem smul_evalSt_empty (k : ℤ) :
    (V2m 4 four_ge_one).smul Uc k (evalSt [(-1, []), (1, [])]) = 0 := by
  have h : evalSt [(-1, []), (1, [])] = 0 := by
    simp [evalSt_cons, PlusUnitary.evRc_nil]
  rw [h, PreVertexAlgebra.smul_zero_right]

/-- The `V₈` telescope of the weight-nine generator on `h(-1)1`. -/
theorem telescope_V8 (hc : V8OuterCertificates) :
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
  have o0 := outer_of_cert 0 (by norm_num) Z0 _ inner_0 Z_sectors_0 hc.1
  have o1 := outer_of_cert 1 (by norm_num) Z1 _ inner_1 Z_sectors_1 hc.2.1
  have o2 := outer_of_cert 2 (by norm_num) Z2 _ inner_2 Z_sectors_2 hc.2.2.1
  have o3 := outer_of_cert 3 (by norm_num) Z3 _ inner_3 Z_sectors_3 hc.2.2.2.1
  have o4 := outer_of_cert 4 (by norm_num) Z4 _ inner_4 Z_sectors_4 hc.2.2.2.2
  have o5 := outer_5
  norm_num only at o0 o1 o2 o3 o4 o5 ⊢
  rw [o0, o1, o2, o3, o4, o5]
  simp only [smul_smul, ← add_smul]
  norm_num [Nat.choose]

theorem telescope_value_ne_zero : (-345600 : ℂ) ≠ 0 := by norm_num

/-- `CubicVacuumTelescope` from the Zhu inputs and the five decidable outer certificates. -/
theorem cubicVacuumTelescope_of_zhu (hc : V8OuterCertificates)
    (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable) : CubicVacuumTelescope :=
  cubicVacuumTelescope_of_V8 hC2 hdim htab telescope_value_ne_zero (telescope_V8 hc)

/-- The resonant pair `(1 ↘ 0)` of the tetrahedral model splits from the Zhu inputs alone. -/
theorem cubic_pair_one_zero_of_zhu (hc : V8OuterCertificates)
    (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable) :
    PlusRat2Dual.PairSplit cubicModel 1 0 :=
  cubic_pair_one_zero hC2 hdim htab (cubicVacuumTelescope_of_zhu hc hC2 hdim htab)

/-- Rationality of the tetrahedral model from `C₂`, the two Zhu inputs, and the two
non-vacuum resonant pairs. -/
theorem cubicModel_admissiblyRational_of_zhu (hc : V8OuterCertificates)
    (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable)
    (hnv : CubicNonVacuumPairs) : AdmissiblyRational cubicModel :=
  cubicModel_admissiblyRational_of_reduced hC2 hdim htab
    (cubicVacuumTelescope_of_zhu hc hC2 hdim htab) hnv

theorem cubicModelRationalOfC2_of_zhu (hc : V8OuterCertificates) (hdim : CubicZhuDimensionBound)
    (htab : CubicZhuCharacterTable) (hnv : CubicNonVacuumPairs) : CubicModelRationalOfC2 :=
  fun hC2 => cubicModel_admissiblyRational_of_zhu hc hC2 hdim htab hnv

end VOA.Classification.COne.OrbRat3
