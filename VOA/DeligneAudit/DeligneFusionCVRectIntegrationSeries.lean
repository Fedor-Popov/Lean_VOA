import VOA.DeligneAudit.DeligneFusionCVRectIntegrationPrimitive

/-!
# Polynomial functional currents for the integration recursion

The chosen zero-mode is the inner polynomial variable. Coefficientwise
formal differentiation gives an actual derivation of its outer current
series, allowing the normalized primitive's functional identity to be
applied to the two-current product.
-/

namespace VOA.DeligneAudit.A2.CVRectIntegrationSeries

noncomputable section

section Series

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C]

/-- Apply a linear functional or operator coefficientwise, without
requiring it to preserve multiplication. -/
def linearSeries (f : B →ₗ[ℂ] C) : PowerSeries B →ₗ[ℂ] PowerSeries C where
  toFun S := PowerSeries.mk fun j => f (PowerSeries.coeff j S)
  map_add' S T := by ext j; simp
  map_smul' c S := by ext j; simp

@[simp] theorem coeff_linearSeries (f : B →ₗ[ℂ] C) (S : PowerSeries B) (j : ℕ) :
    PowerSeries.coeff j (linearSeries f S) = f (PowerSeries.coeff j S) := by
  simp only [linearSeries, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]

theorem linearSeries_C (f : B →ₗ[ℂ] C) (b : B) :
    linearSeries f (PowerSeries.C b) = PowerSeries.C (f b) := by
  ext j
  simp only [coeff_linearSeries, PowerSeries.coeff_C]
  split_ifs <;> simp

theorem linearSeries_shift (f : B →ₗ[ℂ] C) (S : PowerSeries B) (h : ℕ) :
    linearSeries f (PowerSeries.X ^ h * S) = PowerSeries.X ^ h * linearSeries f S := by
  ext j
  simp only [coeff_linearSeries, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

/-- Coefficientwise extension of an actual derivation to current series. -/
def seriesDerivation (D : Derivation ℂ B B) : Derivation ℂ (PowerSeries B) (PowerSeries B) where
  toLinearMap := linearSeries D.toLinearMap
  map_one_eq_zero' := by
    ext j
    simp only [linearSeries, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_one]
    split_ifs <;> simp
  leibniz' S T := by
    ext j
    simp only [linearSeries, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk,
      smul_eq_mul, map_add, PowerSeries.coeff_mul, map_sum, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · rfl
    · exact Finset.Nat.sum_antidiagonal_swap (n := j)
        (f := fun p => PowerSeries.coeff p.1 T * D (PowerSeries.coeff p.2 S))

@[simp] theorem coeff_seriesDerivation (D : Derivation ℂ B B)
    (S : PowerSeries B) (j : ℕ) :
    PowerSeries.coeff j (seriesDerivation D S) = D (PowerSeries.coeff j S) := by
  change PowerSeries.coeff j (linearSeries D.toLinearMap S) = _
  simp only [coeff_linearSeries, Derivation.coeFn_coe]

theorem seriesDerivation_C (D : Derivation ℂ B B) (b : B) :
    seriesDerivation D (PowerSeries.C b) = PowerSeries.C (D b) :=
  linearSeries_C D.toLinearMap b

theorem seriesDerivation_X (D : Derivation ℂ B B) :
    seriesDerivation D PowerSeries.X = 0 := by
  ext j
  simp only [coeff_seriesDerivation, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp

end Series

section Polynomial

open VOA.DeligneAudit.A2.CVRectIntegrationPrimitive

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The actual derivative in the inner, distinguished zero-mode variable. -/
def innerDerivative : Derivation ℂ (Polynomial A) (Polynomial A) where
  toLinearMap := (Polynomial.derivative : Polynomial A →ₗ[A] Polynomial A).restrictScalars ℂ
  map_one_eq_zero' := Polynomial.derivative_one
  leibniz' p q := by
    change Polynomial.derivative (p * q) = p * Polynomial.derivative q + q * Polynomial.derivative p
    rw [Polynomial.derivative_mul]
    ring

/-- An actual source functional killing the zero-mode-free subspace
factors coefficientwise through the inner derivative and normalized primitive. -/
theorem functional_series_derivative (ℓ : Polynomial A →ₗ[ℂ] ℂ)
    (hℓ : ∀ a : A, ℓ (Polynomial.C a) = 0) (S : PowerSeries (Polynomial A)) :
    linearSeries ℓ S =
      linearSeries (ℓ.comp primitive) (seriesDerivation innerDerivative S) := by
  ext j
  simp only [coeff_linearSeries, coeff_seriesDerivation]
  exact functional_derivative_identity ℓ hℓ _

theorem derivative_multiplier (i : ℕ) (B : A) :
    innerDerivative (Polynomial.X ^ i * Polynomial.C B) =
      i • (Polynomial.X ^ (i - 1) * Polynomial.C B) := by
  change Polynomial.derivative _ = _
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_C,
    mul_zero, add_zero, Polynomial.C_eq_natCast, nsmul_eq_mul]
  ring

/-- A current all of whose coefficients are independent of the zero-mode. -/
def constantCurrent (f : PowerSeries A) : PowerSeries (Polynomial A) :=
  PowerSeries.map Polynomial.C f

theorem derivative_constantCurrent (f : PowerSeries A) :
    seriesDerivation innerDerivative (constantCurrent f) = 0 := by
  apply PowerSeries.ext
  intro j
  simp only [coeff_seriesDerivation, constantCurrent, PowerSeries.coeff_map, map_zero]
  change Polynomial.derivative (Polynomial.C (PowerSeries.coeff j f)) = 0
  exact Polynomial.derivative_C

/-- The selected reversed current has its zero-mode at degree `h`.
Every other coefficient belongs to the algebra of the other modes. -/
def chosenCurrent (h : ℕ) (f : PowerSeries A) : PowerSeries (Polynomial A) :=
  PowerSeries.C Polynomial.X * PowerSeries.X ^ h + constantCurrent f

theorem derivative_chosenCurrent (h : ℕ) (f : PowerSeries A) :
    seriesDerivation innerDerivative (chosenCurrent h f) = PowerSeries.X ^ h := by
  unfold chosenCurrent
  rw [map_add, Derivation.leibniz, Derivation.leibniz_pow, seriesDerivation_X]
  simp only [smul_zero, zero_add, add_zero, seriesDerivation_C, derivative_constantCurrent]
  change PowerSeries.X ^ h * PowerSeries.C (Polynomial.derivative Polynomial.X) = _
  simp only [Polynomial.derivative_X, map_one, mul_one]

/-- The functional value of a current product with an arbitrary monomial
in the chosen zero-mode variable and arbitrary other-mode coefficient. -/
def functionalCurrent (ℓ : Polynomial A →ₗ[ℂ] ℂ) (B : A)
    (S T : PowerSeries (Polynomial A)) (a b i : ℕ) : PowerSeries ℂ :=
  linearSeries ℓ (PowerSeries.C (Polynomial.X ^ i * Polynomial.C B) * S ^ a * T ^ b)

/-- The actual polynomial primitive gives the derivative recurrence used
in the two order inductions. No target relation or ideal preservation is a premise. -/
theorem functionalCurrent_recurrence (ℓ : Polynomial A →ₗ[ℂ] ℂ)
    (hℓ : ∀ B : A, ℓ (Polynomial.C B) = 0)
    (S T : PowerSeries (Polynomial A)) (h : ℕ)
    (hS : seriesDerivation innerDerivative S = PowerSeries.X ^ h)
    (hT : seriesDerivation innerDerivative T = 0)
    (B : A) (a b i : ℕ) :
    functionalCurrent ℓ B S T a b i =
      (i : ℂ) • functionalCurrent (ℓ.comp primitive) B S T a b (i - 1) +
      (a : ℂ) • (PowerSeries.X ^ h *
        functionalCurrent (ℓ.comp primitive) B S T (a - 1) b i) := by
  let D := seriesDerivation (innerDerivative (A := A))
  have hD : D (PowerSeries.C (Polynomial.X ^ i * Polynomial.C B) * S ^ a * T ^ b) =
      i • (PowerSeries.C (Polynomial.X ^ (i - 1) * Polynomial.C B) * S ^ a * T ^ b) +
      a • (PowerSeries.X ^ h *
        (PowerSeries.C (Polynomial.X ^ i * Polynomial.C B) * S ^ (a - 1) * T ^ b)) := by
    simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
    rw [show D S = PowerSeries.X ^ h from hS, show D T = 0 from hT]
    rw [show D (PowerSeries.C (Polynomial.X ^ i * Polynomial.C B)) =
      PowerSeries.C (i • (Polynomial.X ^ (i - 1) * Polynomial.C B)) from
      (seriesDerivation_C _ _).trans (congrArg PowerSeries.C (derivative_multiplier i B))]
    simp only [nsmul_eq_mul, map_mul, map_natCast, mul_zero]
    ring
  unfold functionalCurrent
  rw [functional_series_derivative ℓ hℓ, hD, map_add, map_nsmul, map_nsmul,
    linearSeries_shift]
  simp only [Nat.cast_smul_eq_nsmul ℂ]

end Polynomial

end

end VOA.DeligneAudit.A2.CVRectIntegrationSeries

#print axioms VOA.DeligneAudit.A2.CVRectIntegrationSeries.seriesDerivation
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationSeries.functional_series_derivative
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationSeries.functionalCurrent_recurrence
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationSeries.derivative_chosenCurrent
