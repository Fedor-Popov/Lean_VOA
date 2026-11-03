import VOA.DeligneAudit.DeligneFusionCVRectIntegrationOrder

/-!
# The actual normalized polynomial primitive

The distinguished zero-mode variable is the polynomial variable over
the algebra of all other current modes. Its normalized primitive is a
linear operator, not multiplication by that variable. This file records
its exact derivative identities and their consequence for functionals
which annihilate the zero-mode-free subspace.
-/

namespace VOA.DeligneAudit.A2.CVRectIntegrationPrimitive

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Integrate in the distinguished zero-mode variable, with zero constant term. -/
def primitive : (Polynomial A) →ₗ[ℂ] (Polynomial A) :=
  Polynomial.lsum fun n => ((n + 1 : ℕ) : ℂ)⁻¹ •
    (Polynomial.monomial (n + 1) : A →ₗ[A] (Polynomial A)).restrictScalars ℂ

theorem primitive_monomial (n : ℕ) (a : A) :
    primitive (Polynomial.monomial n a) =
      ((n + 1 : ℕ) : ℂ)⁻¹ • Polynomial.monomial (n + 1) a := by
  simp [primitive, Polynomial.lsum, Polynomial.sum_monomial_index]

theorem derivative_monomial_succ_smul (n : ℕ) (a : A) :
    Polynomial.derivative (Polynomial.monomial (n + 1) a) =
      ((n + 1 : ℕ) : ℂ) • Polynomial.monomial n a := by
  rw [Polynomial.derivative_monomial_succ]
  rw [Nat.cast_smul_eq_nsmul ℂ]
  simp only [Polynomial.smul_monomial, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]

/-- The derivative of the actual primitive is exactly its input. -/
theorem derivative_primitive (p : (Polynomial A)) : Polynomial.derivative (primitive p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
      rw [primitive_monomial, Polynomial.derivative_smul, derivative_monomial_succ_smul,
        smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul]

/-- Integrating a derivative removes exactly the constant term. -/
theorem primitive_derivative (p : (Polynomial A)) :
    primitive (Polynomial.derivative p) = p - Polynomial.C (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.coeff_add]
      abel
  | monomial n a =>
      cases n with
      | zero => simp only [Polynomial.monomial_zero_left, Polynomial.derivative_C, map_zero,
          Polynomial.coeff_C_zero, sub_self]
      | succ n =>
          rw [derivative_monomial_succ_smul, map_smul, primitive_monomial, smul_smul,
            mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul]
          simp only [Polynomial.coeff_monomial, Nat.add_one_ne_zero, if_false,
            map_zero, sub_zero]

/-- A functional killing every zero-mode-free polynomial factors through
the derivative using the actual normalized primitive. -/
theorem functional_derivative_identity (ℓ : (Polynomial A) →ₗ[ℂ] ℂ)
    (hℓ : ∀ a : A, ℓ (Polynomial.C a) = 0) (p : (Polynomial A)) :
    ℓ p = (ℓ.comp primitive) (Polynomial.derivative p) := by
  rw [LinearMap.comp_apply, primitive_derivative, map_sub, hℓ, sub_zero]

end

end VOA.DeligneAudit.A2.CVRectIntegrationPrimitive

#print axioms VOA.DeligneAudit.A2.CVRectIntegrationPrimitive.derivative_primitive
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationPrimitive.primitive_derivative
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationPrimitive.functional_derivative_identity
