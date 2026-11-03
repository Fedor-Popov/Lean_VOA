import VOA.DeligneAudit.SL4TAlternantFactorization

/-! # Consecutive moment minors generate arbitrary moment minors -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Pair a polynomial with independent sequences of moments in its variables. -/
def polynomialMomentPairing {j : ℕ} (v : Fin j → ℕ → A) :
    MvPolynomial (Fin j) A →ₗ[A] A :=
  Finsupp.linearCombination A (fun d : Fin j →₀ ℕ => ∏ b, v b (d b))

theorem polynomialMomentPairing_monomial {j : ℕ} (v : Fin j → ℕ → A)
    (d : Fin j →₀ ℕ) (a : A) :
    polynomialMomentPairing v (MvPolynomial.monomial d a) = a * ∏ b, v b (d b) := by
  exact Finsupp.linearCombination_single A a d

/-- A monomial translates each of the moment indices independently. -/
theorem polynomialMomentPairing_monomial_mul {j : ℕ} (v : Fin j → ℕ → A)
    (d : Fin j →₀ ℕ) (a : A) (p : MvPolynomial (Fin j) A) :
    polynomialMomentPairing v (MvPolynomial.monomial d a * p) =
      a * polynomialMomentPairing (fun b n => v b (d b + n)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [MvPolynomial.monomial_mul, polynomialMomentPairing_monomial,
        polynomialMomentPairing_monomial]
      simp only [Finsupp.add_apply, mul_assoc]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]

theorem polynomialMomentPairing_power_product {j : ℕ} (v : Fin j → ℕ → A)
    (d : Fin j → ℕ) :
    polynomialMomentPairing v (∏ b, (MvPolynomial.X b) ^ d b) = ∏ b, v b (d b) := by
  classical
  rw [MvPolynomial.prod_X_pow, polynomialMomentPairing_monomial, one_mul]
  apply Finset.prod_congr rfl
  intro b hb
  simp

/-- Pairing a power alternant gives the corresponding moment determinant. -/
theorem polynomialMomentPairing_power_determinant {j : ℕ} (v : Fin j → ℕ → A)
    (rows : Fin j → ℕ) :
    polynomialMomentPairing v
        (Matrix.det fun a b : Fin j => (MvPolynomial.X b) ^ rows a) =
      Matrix.det (fun a b : Fin j => v b (rows a)) := by
  classical
  simp only [Matrix.det_apply, Units.smul_def, map_sum, map_zsmul,
    polynomialMomentPairing_power_product]

/-- Consecutive-row minors of all shifted columns control every choice of moment rows. -/
theorem moment_determinant_mem_of_consecutive {j : ℕ} (v : Fin j → ℕ → A)
    (I : Ideal A)
    (hI : ∀ d : Fin j → ℕ, Matrix.det (fun a b : Fin j => v b (d b + a.val)) ∈ I)
    (rows : Fin j → ℕ) : Matrix.det (fun a b : Fin j => v b (rows a)) ∈ I := by
  classical
  obtain ⟨s, hs⟩ := polynomial_alternant_factor j
    (fun a => (Polynomial.X : Polynomial A) ^ rows a)
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X] at hs
  rw [← polynomialMomentPairing_power_determinant v rows, hs]
  clear hs
  induction s using MvPolynomial.induction_on' with
  | monomial d a =>
      rw [polynomialMomentPairing_monomial_mul, polynomialMomentPairing_power_determinant]
      exact I.mul_mem_left a (hI d)
  | add p q hp hq =>
      rw [add_mul, map_add]
      exact I.add_mem hp hq

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomialMomentPairing_monomial
#print axioms VOA.DeligneAudit.SL4T.polynomialMomentPairing_monomial_mul
#print axioms VOA.DeligneAudit.SL4T.polynomialMomentPairing_power_product
#print axioms VOA.DeligneAudit.SL4T.polynomialMomentPairing_power_determinant
#print axioms VOA.DeligneAudit.SL4T.moment_determinant_mem_of_consecutive
