import VOA.Classification.COne.QExpThetaFourier

/-!
# An integral weight-one unit and weight raising

At positive levels divisible by 24 the (N/4, 0) Eisenstein series, scaled by
2/N, has constant coefficient 1 and integral positive coefficients. Division
by its powers preserves any integer coefficient module. No spanning result
in higher weight is assumed or proved by the unit construction.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.SSHecke

def spanQuarterIndex {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N / 4, Nat.div_lt_self hN (by norm_num)⟩

/-- Integral coefficients of the normalized quarter-torsion series. -/
def spanUnitCoeff (N n : ℕ) : ℤ :=
  if n = 0 then 1 else 4 * ∑ t ∈ n.divisors,
    ((if t % N = N / 4 then 1 else 0) -
      (if (t + N / 4) % N = 0 then 1 else 0))

def spanUnitSeries (N : ℕ) : PowerSeries ℤ := PowerSeries.mk (spanUnitCoeff N)

theorem spanUnitSeries_constantCoeff (N : ℕ) :
    PowerSeries.constantCoeff (spanUnitSeries N) = 1 := by
  simp [spanUnitSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, spanUnitCoeff]

/-- A genuine full-level modular form, with no residual slash-law hypothesis. -/
def spanWeightOneUnit {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1 :=
  (2 / (N : ℂ)) • weightOneModularForm hN
    (Complex.isPrimitiveRoot_exp N hN.ne')
    (fullLevelWeightOneSlash24 N hN h24 _ (Complex.isPrimitiveRoot_exp N hN.ne'))
    (spanQuarterIndex hN) ⟨0, hN⟩

theorem spanWeightOneUnit_coeff {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) (n : ℕ) :
    (qExpansion (N : ℝ) (spanWeightOneUnit hN h24)).coeff n =
      (spanUnitCoeff N n : ℂ) := by
  have h4 : 4 ∣ N := dvd_trans (by norm_num : 4 ∣ 24) h24
  have hdiv : N / 4 * 4 = N := Nat.div_mul_cancel h4
  have ha : N / 4 ≠ 0 := by omega
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hdivC : (N : ℂ) = (N / 4 : ℕ) * 4 := by exact_mod_cast hdiv.symm
  let E := weightOneModularForm hN (Complex.isPrimitiveRoot_exp N hN.ne')
    (fullLevelWeightOneSlash24 N hN h24 _ (Complex.isPrimitiveRoot_exp N hN.ne'))
    (spanQuarterIndex hN) ⟨0, hN⟩
  have hs : qExpansion (N : ℝ) (spanWeightOneUnit hN h24) =
      (2 / (N : ℂ)) • qExpansion (N : ℝ) E :=
    ModularForm.qExpansion_smul (by exact_mod_cast hN)
      (nat_mem_strictPeriods_Gamma N) (2 / (N : ℂ)) E
  rw [hs, PowerSeries.coeff_smul, weightOneModularForm_coeff]
  change 2 / (N : ℂ) * weightOneIntegralCoeff N (weightOneStandardRoot N)
    (spanQuarterIndex hN) ⟨0, hN⟩ n = _
  by_cases hn : n = 0
  · subst n
    simp only [weightOneIntegralCoeff, spanQuarterIndex, ha, false_and, ↓reduceIte,
      spanUnitCoeff, Int.cast_one]
    field_simp
    linear_combination hdivC
  · have hroot : weightOneStandardRoot N ^ N = 1 :=
      (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
    have hd : weightOneDivisorCoeff N (weightOneStandardRoot N)
        (spanQuarterIndex hN) ⟨0, hN⟩ n =
        ((∑ t ∈ n.divisors,
          ((if t % N = N / 4 then 1 else 0) -
           (if (t + N / 4) % N = 0 then 1 else 0)) : ℤ) : ℂ) := by
      simp [weightOneDivisorCoeff, spanQuarterIndex, pow_mul,
        hroot, mul_comm (n / _) N]
    simp only [weightOneIntegralCoeff, spanQuarterIndex, ha, false_and, ↓reduceIte,
      hn, weightOneScale] at ⊢
    simp only [spanQuarterIndex] at hd
    rw [hd]
    simp only [spanUnitCoeff, hn, ↓reduceIte, Int.cast_mul, Int.cast_ofNat]
    field_simp
    ring

theorem spanWeightOneUnit_qExpansion {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) :
    qExpansion (N : ℝ) (spanWeightOneUnit hN h24) =
      PowerSeries.map (Int.castRingHom ℂ) (spanUnitSeries N) := by
  ext n
  simp [spanWeightOneUnit_coeff, spanUnitSeries]

theorem spanWeightOneUnit_ne_zero {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) :
    spanWeightOneUnit hN h24 ≠ 0 := by
  intro h
  have hc := spanWeightOneUnit_coeff hN h24 0
  rw [h] at hc
  change (qExpansion (N : ℝ) (0 : ℍ → ℂ)).coeff 0 = _ at hc
  rw [qExpansion_zero] at hc
  norm_num [spanUnitCoeff] at hc

/-- Division by a power preserves the same integer module, with no finiteness
or denominator assumptions on that module. -/
theorem coeff_mem_of_mul_spanUnit_pow {N j : ℕ} {a : PowerSeries ℂ}
    (L : Submodule ℤ ℂ)
    (h : ∀ n, (a * (PowerSeries.map (Int.castRingHom ℂ)
      (spanUnitSeries N)) ^ j).coeff n ∈ L) :
    ∀ n, a.coeff n ∈ L := by
  apply coeff_mem_of_mul_unit (spanUnitSeries N ^ j)
  · simp [spanUnitSeries_constantCoeff]
  · simpa only [map_pow] using h

/-- Weight raising by the integral unit can be reversed on full-level forms. -/
theorem coeff_mem_of_weightRaise {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k)
    (j : ℕ) (L : Submodule ℤ ℂ)
    (h : ∀ n, (qExpansion (N : ℝ)
      (F.mul ((spanWeightOneUnit hN h24).pow j))).coeff n ∈ L) :
    ∀ n, (qExpansion (N : ℝ) F).coeff n ∈ L := by
  apply coeff_mem_of_mul_spanUnit_pow (j := j) L
  simpa only [ModularForm.qExpansion_mul (by exact_mod_cast hN)
    (nat_mem_strictPeriods_Gamma N), ModularForm.qExpansion_pow (by exact_mod_cast hN)
    (nat_mem_strictPeriods_Gamma N), spanWeightOneUnit_qExpansion] using h

/-- In particular no new denominator is introduced by reversing weight raising. -/
theorem awayCoeff_of_weightRaise {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (j M : ℕ) (L : Submodule ℤ ℂ)
    (h : ∀ n, (qExpansion (N : ℝ)
      ((restrictGamma1ToGamma hN F).mul ((spanWeightOneUnit hN h24).pow j))).coeff n
        ∈ awaySat M L) :
    ∀ n, (qExpansion 1 F).coeff n ∈ awaySat M L := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hc := coeff_mem_of_weightRaise hN h24 (restrictGamma1ToGamma hN F) j
    (awaySat M L) h
  intro n
  rw [← qExpansion_coeff_nat_mul hN F n]
  exact hc (N * n)

end VOA.Classification.COne.SSHecke
