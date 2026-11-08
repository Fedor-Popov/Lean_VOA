import VOA.Moonshine.MoonshineCNHyperbolicFock
import VOA.Moonshine.AutFockEigen

/-! # The scalar commutant of the hyperbolic oscillator representation

This is the commutant step of the hyperbolic Fock space construction (blueprint
`Notes/moonshine/MOON_NOGHOST.md`): an operator commuting with the nonzero oscillator modes is
a scalar. No finite-dimensionality, continuity, or assumption about a Sugawara operator is
needed.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial HeisenbergN

theorem hypPolynomial_eq_constant_of_pderiv_zero (p : hypFock)
    (hp : ∀ v : ℕ × Fin 2, pderiv v p = 0) : p = MvPolynomial.C (coeff 0 p) := by
  classical
  have hcoeff (d : (ℕ × Fin 2) →₀ ℕ) (hd : d ≠ 0) : coeff d p = 0 := by
    by_contra hc
    apply hd
    ext v
    have he := coeff_X_mul_pderiv_self v d p
    rw [hp v, mul_zero, coeff_zero] at he
    have hz : (d v : ℂ) = 0 := (mul_eq_zero.mp he.symm).resolve_right hc
    exact_mod_cast hz
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · simp [coeff_C, Ne.symm hd, hcoeff d hd]

theorem hypCommutant_mul_variable (D : Module.End ℂ hypFock) (charges : Fin 2 → ℂ)
    (hD : ∀ a n, n ≠ 0 → D * hypOscillator a (charges a) n =
      hypOscillator a (charges a) n * D) (v : ℕ × Fin 2) (p : hypFock) :
    D (X v * p) = X v * D p := by
  have he := LinearMap.congr_fun (hD v.2 (-(v.1 + 1 : ℤ)) (by omega)) p
  simpa only [Module.End.mul_apply, hypOscillator_negative_apply] using he

theorem hypCommutant_mul_one (D : Module.End ℂ hypFock) (charges : Fin 2 → ℂ)
    (hD : ∀ a n, n ≠ 0 → D * hypOscillator a (charges a) n =
      hypOscillator a (charges a) n * D) (p : hypFock) :
    D p = p * D 1 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (MvPolynomial.C c : hypFock) = c • 1 from by simp [smul_eq_C_mul], map_smul]
    simp [smul_eq_C_mul]
  | add p q hp hq => rw [map_add, hp, hq, add_mul]
  | mul_X p v hp =>
    rw [mul_comm p (X v), hypCommutant_mul_variable D charges hD, hp]
    ring

theorem hypCommutant_constant (D : Module.End ℂ hypFock) (charges : Fin 2 → ℂ)
    (hD : ∀ a n, n ≠ 0 → D * hypOscillator a (charges a) n =
      hypOscillator a (charges a) n * D) : D 1 = MvPolynomial.C (coeff 0 (D 1)) := by
  apply hypPolynomial_eq_constant_of_pderiv_zero
  intro v
  have he := LinearMap.congr_fun (hD v.2.rev (v.1 + 1 : ℤ) (by omega)) 1
  simp only [Module.End.mul_apply, hypOscillator_positive_apply, Fin.rev_rev,
    pderiv_one, smul_zero, map_zero] at he
  have hn : (v.1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero v.1
  exact (smul_eq_zero.mp he.symm).resolve_left hn

/-- Every endomorphism commuting with the nonzero oscillators is scalar. -/
theorem hypCommutant_scalar (D : Module.End ℂ hypFock) (charges : Fin 2 → ℂ)
    (hD : ∀ a n, n ≠ 0 → D * hypOscillator a (charges a) n =
      hypOscillator a (charges a) n * D) :
    D = coeff 0 (D 1) • LinearMap.id := by
  apply LinearMap.ext
  intro p
  rw [hypCommutant_mul_one D charges hD, hypCommutant_constant D charges hD]
  simp [smul_eq_C_mul, mul_comm]

/-- Commuting operators with zero vacuum value vanish identically. -/
theorem hypCommutant_eq_zero_of_vacuum (D : Module.End ℂ hypFock) (charges : Fin 2 → ℂ)
    (hD : ∀ a n, n ≠ 0 → D * hypOscillator a (charges a) n =
      hypOscillator a (charges a) n * D) (h1 : D 1 = 0) : D = 0 := by
  rw [hypCommutant_scalar D charges hD, h1, coeff_zero, zero_smul]

end VOA.Moonshine.ConwayNorton
