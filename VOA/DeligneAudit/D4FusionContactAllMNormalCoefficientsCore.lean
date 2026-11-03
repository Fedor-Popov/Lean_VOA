import VOA.DeligneAudit.D4FusionContactAllMWheelsCore
import Mathlib.RingTheory.PowerSeries.Basic

/-! Constant-current derivation transport of whole cubic coefficients.
Finite convolution is retained; no coefficient is split into monomial relations. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def cubeCoeff (U : ℕ → A) (s : ℕ) : A :=
  PowerSeries.coeff s (PowerSeries.mk U ^ 3)

omit [Algebra ℂ A] in
theorem cubeCoeff_formula (U : ℕ → A) (s : ℕ) :
    cubeCoeff U s = ∑ a ∈ Finset.antidiagonal s,
      ∑ b ∈ Finset.antidiagonal a.1, U b.1 * U b.2 * U a.2 := by
  simp only [cubeCoeff, pow_succ, pow_zero, one_mul, PowerSeries.coeff_mul,
    PowerSeries.coeff_mk, Finset.sum_mul]

theorem third_deriv_product (D : Derivation ℂ A A) (u₁ u₂ u₃ v₁ v₂ v₃ : A)
    (h₁ : D u₁ = v₁) (h₂ : D u₂ = v₂) (h₃ : D u₃ = v₃)
    (hv₁ : D v₁ = 0) (hv₂ : D v₂ = 0) (hv₃ : D v₃ = 0) :
    D (D (D (u₁ * u₂ * u₃))) = 6 * (v₁ * v₂ * v₃) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add,
    h₁, h₂, h₃, hv₁, hv₂, hv₃, mul_zero, add_zero, zero_add]
  ring

theorem third_deriv_cubeCoeff (D : Derivation ℂ A A) (U V : ℕ → A)
    (hU : ∀ r, D (U r) = V r) (hV : ∀ r, D (V r) = 0) (s : ℕ) :
    D (D (D (cubeCoeff U s))) = 6 * cubeCoeff V s := by
  simp only [cubeCoeff_formula, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact third_deriv_product D _ _ _ _ _ _ (hU _) (hU _) (hU _) (hV _) (hV _) (hV _)

theorem third_deriv_cubeCoeff_nsmul (D : Derivation ℂ A A) (U V : ℕ → A)
    (hU : ∀ r, D (U r) = V r) (hV : ∀ r, D (V r) = 0) (s : ℕ) :
    D (D (D (cubeCoeff U s))) = (6 : ℕ) • cubeCoeff V s := by
  simpa only [nsmul_eq_mul] using third_deriv_cubeCoeff D U V hU hV s

omit [Algebra ℂ A] in
theorem cubeCoeff_neg (U : ℕ → A) (s : ℕ) :
    cubeCoeff (fun r => -U r) s = -cubeCoeff U s := by
  have he : PowerSeries.mk (fun r => -U r) = -(PowerSeries.mk U) := by
    ext r
    simp only [PowerSeries.coeff_mk, map_neg]
  rw [cubeCoeff, he, show (-(PowerSeries.mk U)) ^ 3 = -(PowerSeries.mk U ^ 3) by ring,
    map_neg]
  rfl

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.third_deriv_cubeCoeff
