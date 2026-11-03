import VOA.DeligneAudit.SL4TMixedCellFiltration

/-! # Nilpotent power sums of the mixed characteristic alphabet -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- Equal characteristic products of equal total length have equal ascending series. -/
theorem coefficient_product_of_descending (f g u v : ℕ → R) (d e j k : ℕ)
    (hlen : d + e = j + k)
    (h : descendingPoly f d * descendingPoly g e = descendingPoly u j * descendingPoly v k) :
    coefficientPoly f d * coefficientPoly g e = coefficientPoly u j * coefficientPoly v k := by
  unfold descendingPoly at h
  rw [← reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _),
    ← reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _)] at h
  rw [hlen] at h
  have ht := congrArg (reflect (j + k)) h
  simpa only [reflect_reflect] using ht

/-- Complementary characteristic factors give inverse ascending coefficient series. -/
theorem coefficient_product_one_of_descending (f g : ℕ → R) (d e : ℕ)
    (h : descendingPoly f d * descendingPoly g e = X ^ (d + e)) :
    coefficientPoly f d * coefficientPoly g e = 1 := by
  unfold descendingPoly at h
  rw [← reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _)] at h
  have ht := congrArg (reflect (d + e)) h
  simpa only [reflect_reflect, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero] using ht

/-- Both ascending series of a base alphabet are units. -/
theorem mixedBase_series_units (q : MixedParams) (hq : MixedValid q) (i : Fin 3) :
    IsUnit (coefficientPoly
      (fun j => (-1) ^ j * mixedEvaluation q (mixedE (mixedBaseIndex i) j))
      (mixedBaseLength q i).toNat) ∧
    IsUnit (coefficientPoly (fun j => mixedEvaluation q (mixedH (mixedBaseIndex i) j))
      (mixedBaseSize q i - mixedBaseLength q i).toNat) := by
  have hv := mixedBase_valid q hq i
  have hlen : (mixedBaseSize q i).toNat = (mixedBaseLength q i).toNat +
      (mixedBaseSize q i - mixedBaseLength q i).toNat := by omega
  have h := mixedBase_characteristic_product q hq i
  rw [hlen] at h
  have ht := coefficient_product_one_of_descending _ _ _ _ h
  exact (Commute.all _ _).isUnit_mul_iff.mp (ht.symm ▸ isUnit_one)

/-- The two relative characteristic alphabets have unit ascending series. -/
theorem mixedRelative_series_units (q : MixedParams) (hq : MixedValid q) :
    IsUnit (coefficientPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedE 3 j))
      q.e1.toNat) ∧
    IsUnit (coefficientPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedG2prime j))
      (mixedQ q - q.e2).toNat) := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  constructor
  · have hlen : q.e1.toNat + (mixedP q - q.e1).toNat =
        q.d1.toNat + (q.B - q.d2).toNat := by simp only [mixedP]; omega
    have ht := coefficient_product_of_descending _ _ _ _ _ _ _ _ hlen
      (mixedFirst_relative_factorization q hq)
    have hu := (mixedBase_series_units q hq 0).1.mul (mixedBase_series_units q hq 1).2
    apply isUnit_of_mul_isUnit_left
    rw [ht]
    exact hu
  · have hlen : q.e2.toNat + (mixedQ q - q.e2).toNat =
        q.d2.toNat + (q.A - q.d3).toNat := by simp only [mixedQ]; omega
    have ht := coefficient_product_of_descending _ _ _ _ _ _ _ _ hlen
      (mixedSecond_relative_factorization q hq)
    have hu := (mixedBase_series_units q hq 1).1.mul (mixedBase_series_units q hq 2).2
    apply isUnit_of_mul_isUnit_right
    rw [ht]
    exact hu

/-- The ascending coefficient series of the full characteristic alphabet. -/
def mixedCoefficientSeries (q : MixedParams) : (MixedRing q)[X] :=
  coefficientPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedE 3 j)) q.e1.toNat *
    coefficientPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedG2prime j))
      (mixedQ q - q.e2).toNat

theorem mixedCoefficientSeries_unit (q : MixedParams) (hq : MixedValid q) :
    IsUnit (mixedCoefficientSeries q) :=
  (mixedRelative_series_units q hq).1.mul (mixedRelative_series_units q hq).2

theorem mixedCoefficientSeries_zero (q : MixedParams) :
    (mixedCoefficientSeries q).coeff 0 = 1 := by
  obtain ⟨he, _, _, _, _, hg⟩ := mixed_series_zero
  simp [mixedCoefficientSeries, mul_coeff_zero, coefficientPoly_coeff, he, hg]

theorem mixedWeight_length (q : MixedParams) (hq : MixedValid q) :
    (mixedWeight q).toNat = q.e1.toNat + (mixedQ q - q.e2).toNat := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ, mixedWeight] at hv ⊢
  omega

theorem mixedCoefficientSeries_degree (q : MixedParams) (hq : MixedValid q) :
    (mixedCoefficientSeries q).natDegree ≤ (mixedWeight q).toNat := by
  rw [mixedWeight_length q hq]
  exact natDegree_mul_le.trans (Nat.add_le_add (coefficientPoly_degree _ _)
    (coefficientPoly_degree _ _))

/-- Power sums obtained from the signed elementary coefficients by inverse Newton recursion. -/
def mixedPowerSum (q : MixedParams) : ℕ → MixedRing q :=
  powerSumOfCoeff (mixedWeight q).toNat (mixedCoefficientSeries q).coeff

theorem mixedPowerSum_newton (q : MixedParams) (n : ℕ) :
    newtonCoeff (mixedPowerSum q) n = (mixedCoefficientSeries q).coeff n :=
  newtonCoeff_powerSumOfCoeff _ _ (mixedCoefficientSeries_zero q) n

theorem mixedPowerSum_newton_tail (q : MixedParams) (hq : MixedValid q)
    (j : ℕ) (hj : (mixedWeight q).toNat < j) : newtonCoeff (mixedPowerSum q) j = 0 := by
  rw [mixedPowerSum_newton]
  exact coeff_eq_zero_of_natDegree_lt ((mixedCoefficientSeries_degree q hq).trans_lt hj)

/-- Positive power sums are nilpotent without additional hypotheses on the ring image. -/
theorem mixedPowerSum_nilpotent (q : MixedParams) (hq : MixedValid q)
    (s : ℕ) (hs : 1 ≤ s) : IsNilpotent (mixedPowerSum q s) := by
  apply powerSumOfCoeff_nilpotent _ _ _ s hs
  intro j hj
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (mixedCoefficientSeries_unit q hq)).2 j
    (by omega)

/-- The Newton characteristic is exactly the mixed characteristic polynomial. -/
theorem mixedPowerSum_descending (q : MixedParams) (hq : MixedValid q) :
    descendingPoly (newtonCoeff (mixedPowerSum q)) (mixedWeight q).toNat =
      mixedCharacteristic q := by
  simp only [funext (mixedPowerSum_newton q), descendingPoly]
  rw [coefficientPoly_coeffs _ _ (mixedCoefficientSeries_degree q hq),
    mixedWeight_length q hq]
  unfold mixedCoefficientSeries
  rw [reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _)]
  rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.coefficient_product_of_descending
#print axioms VOA.DeligneAudit.SL4T.coefficient_product_one_of_descending
#print axioms VOA.DeligneAudit.SL4T.mixedBase_series_units
#print axioms VOA.DeligneAudit.SL4T.mixedRelative_series_units
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_unit
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_zero
#print axioms VOA.DeligneAudit.SL4T.mixedWeight_length
#print axioms VOA.DeligneAudit.SL4T.mixedCoefficientSeries_degree
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_newton
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_newton_tail
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_nilpotent
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_descending
