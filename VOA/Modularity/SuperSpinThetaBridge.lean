/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinAnalytic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# A theta-characteristic bridge for the spin coefficient `S`-law

Mathlib's `jacobiTheta₂_functional_equation` is the Poisson-summation theorem needed for the
analytic `S` generator.  This file repackages it for arbitrary characteristics `a,b`:

`Theta[a,b](z,tau) = exp(pi*i*a^2*tau + 2*pi*i*a*(z+b))
  * jacobiTheta₂ (z+a*tau+b) tau`.

The proved transformation is

`Theta[a,b](z/tau,-1/tau) = (-i*tau)^(1/2) exp(pi*i*z^2/tau + 2*pi*i*a*b)
  Theta[b,-a](z,tau)`.

For `a,b` equal to `0` or `1/2` these are the four spin characteristics.  The scalar
characteristic phase is independent of `z`; hence it disappears from logarithmic derivatives.
Taking a difference of two theta logarithmic derivatives also cancels the common Gaussian
anomaly.  This is precisely the analytic mechanism behind the homogeneous transformation of
the nontrivial `P_k^{mu,lambda}` family.

No identification with `spinQ` is asserted here.  That last step requires a Jacobi
triple-product/logarithmic-derivative expansion and Taylor-coefficient extraction, which are not
currently present in Mathlib or the repository.
-/

namespace VOA

open Complex

set_option autoImplicit false

/-! ## Theta functions with characteristics -/

/-- Jacobi theta with characteristics `(a,b)`, expressed using Mathlib's two-variable theta. -/
noncomputable def spinThetaChar (a b z tau : Complex) : Complex :=
  Complex.exp (Real.pi * Complex.I * a ^ 2 * tau +
    2 * Real.pi * Complex.I * a * (z + b)) *
      jacobiTheta₂ (z + a * tau + b) tau

/-- The square-root automorphy factor in the Jacobi theta `S` law is nonzero on the upper
half-plane (indeed, whenever `tau` is nonzero). -/
theorem spinThetaSFactor_ne_zero {tau : Complex} (htau : tau ≠ 0) :
    (-Complex.I * tau) ^ (1 / 2 : Complex) ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) htau)

/-- The Mathlib theta functional equation, solved for the transformed theta. -/
theorem jacobiTheta₂_S_solved (w tau : Complex) (htau : tau ≠ 0) :
    jacobiTheta₂ (w / tau) (-1 / tau) =
      (-Complex.I * tau) ^ (1 / 2 : Complex) *
        Complex.exp (Real.pi * Complex.I * w ^ 2 / tau) * jacobiTheta₂ w tau := by
  have hroot := spinThetaSFactor_ne_zero htau
  have hexp : Complex.exp (-Real.pi * Complex.I * w ^ 2 / tau) ≠ 0 := Complex.exp_ne_zero _
  have h := jacobiTheta₂_functional_equation w tau
  calc
    jacobiTheta₂ (w / tau) (-1 / tau)
        = ((-Complex.I * tau) ^ (1 / 2 : Complex) /
            Complex.exp (-Real.pi * Complex.I * w ^ 2 / tau)) * jacobiTheta₂ w tau := by
          apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hroot) hexp)
          rw [h]
          field_simp
    _ = (-Complex.I * tau) ^ (1 / 2 : Complex) *
          Complex.exp (Real.pi * Complex.I * w ^ 2 / tau) * jacobiTheta₂ w tau := by
        rw [div_eq_mul_inv, ← Complex.exp_neg]
        congr 3
        ring

/-- The full characteristic-theta `S` transformation, with every phase explicit. -/
theorem spinThetaChar_S (a b z tau : Complex) (htau : tau ≠ 0) :
    spinThetaChar a b (z / tau) (-1 / tau) =
      (-Complex.I * tau) ^ (1 / 2 : Complex) *
        Complex.exp (Real.pi * Complex.I * z ^ 2 / tau +
          2 * Real.pi * Complex.I * a * b) * spinThetaChar b (-a) z tau := by
  rw [spinThetaChar, spinThetaChar]
  have harg : z / tau + a * (-1 / tau) + b = (z - a + b * tau) / tau := by
    field_simp
    ring
  rw [harg, jacobiTheta₂_S_solved (z - a + b * tau) tau htau]
  simp only [neg_div, one_div]
  have htheta : z - a + b * tau = z + b * tau + -a := by ring
  rw [htheta]
  have hexp :
      Complex.exp (Real.pi * Complex.I * a ^ 2 * -tau⁻¹ +
          2 * Real.pi * Complex.I * a * (z / tau + b)) *
        Complex.exp (Real.pi * Complex.I * (z - a + b * tau) ^ 2 / tau) =
      Complex.exp (Real.pi * Complex.I * z ^ 2 / tau +
          2 * Real.pi * Complex.I * a * b) *
        Complex.exp (Real.pi * Complex.I * b ^ 2 * tau +
          2 * Real.pi * Complex.I * b * (z + -a)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    ring
  rw [htheta] at hexp
  let E₁ := Complex.exp (Real.pi * Complex.I * a ^ 2 * -tau⁻¹ +
    2 * Real.pi * Complex.I * a * (z / tau + b))
  let E₂ := Complex.exp (Real.pi * Complex.I * (z + b * tau + -a) ^ 2 / tau)
  let E₃ := Complex.exp (Real.pi * Complex.I * z ^ 2 / tau +
    2 * Real.pi * Complex.I * a * b)
  let E₄ := Complex.exp (Real.pi * Complex.I * b ^ 2 * tau +
    2 * Real.pi * Complex.I * b * (z + -a))
  let R := (-Complex.I * tau) ^ (1 / 2 : Complex)
  let T := jacobiTheta₂ (z + b * tau + -a) tau
  have hexp' : E₁ * E₂ = E₃ * E₄ := by
    simpa [E₁, E₂, E₃, E₄] using hexp
  calc
    _ = R * (E₁ * E₂) * T := by dsimp [E₁, E₂, R, T]; ring
    _ = R * (E₃ * E₄) * T := by rw [hexp']
    _ = _ := by dsimp [E₃, E₄, R, T]; ring

/-! ## The four sign characteristics -/

/-- The additive theta characteristic represented by a sign phase. -/
noncomputable def spinThetaHalf (s : SpinPhase) : Complex :=
  if s = SpinPhase.plus then 0 else 1 / 2

@[simp] theorem spinThetaHalf_plus : spinThetaHalf SpinPhase.plus = 0 := by
  simp [spinThetaHalf]

@[simp] theorem spinThetaHalf_minus : spinThetaHalf SpinPhase.minus = 1 / 2 := by
  norm_num [spinThetaHalf, SpinPhase.plus, SpinPhase.minus]

/-- The theta function attached to a spin pair.  The two labels remain independent of parity. -/
noncomputable def spinPairTheta (p : SpinPair) (z tau : Complex) : Complex :=
  spinThetaChar (spinThetaHalf p.mu) (spinThetaHalf p.lambda) z tau

/-- `S` swaps the two half-characteristics before reduction of `-a` modulo one.  This is the
exact unreduced formula; reduction introduces only a constant sign, irrelevant to logarithmic
derivatives. -/
theorem spinPairTheta_S_unreduced (p : SpinPair) (z tau : Complex) (htau : tau ≠ 0) :
    spinPairTheta p (z / tau) (-1 / tau) =
      (-Complex.I * tau) ^ (1 / 2 : Complex) *
        Complex.exp (Real.pi * Complex.I * z ^ 2 / tau +
          2 * Real.pi * Complex.I * spinThetaHalf p.mu * spinThetaHalf p.lambda) *
        spinThetaChar (spinThetaHalf p.lambda) (-spinThetaHalf p.mu) z tau := by
  exact spinThetaChar_S _ _ _ _ htau

/-! ## A denominator-free logarithmic-derivative bridge -/

/-- Cross-multiplied logarithmic derivative numerator.  The equality
`thetaCross f g z = 0` says that `f'/f` and `g'/g` agree wherever both denominators are nonzero. -/
noncomputable def thetaCross (f g : Complex → Complex) (z : Complex) : Complex :=
  _root_.deriv f z * g z - _root_.deriv g z * f z

/-- Difference of logarithmic derivatives of two theta characteristics.  The common Gaussian
term in their `S` transformations cancels. -/
noncomputable def spinThetaLogDiff (a b c d tau z : Complex) : Complex :=
  _root_.logDeriv (fun w => spinThetaChar a b w tau) z -
    _root_.logDeriv (fun w => spinThetaChar c d w tau) z

/-- The exact expected homogeneous `S` law for the theta logarithmic-derivative difference,
recorded denominator-free.  This theorem is the analytic kernel transformation needed before
Taylor coefficient extraction. -/
theorem spinThetaCross_S
    (a b c d z tau : Complex) (htauIm : 0 < tau.im) :
    thetaCross
        (fun w => spinThetaChar a b (w / tau) (-1 / tau))
        (fun w => spinThetaChar c d (w / tau) (-1 / tau)) z =
      ((-Complex.I * tau) ^ (1 / 2 : Complex)) ^ 2 *
        Complex.exp (2 * (Real.pi * Complex.I * z ^ 2 / tau) +
          2 * Real.pi * Complex.I * (a * b + c * d)) *
        thetaCross (fun w => spinThetaChar b (-a) w tau)
          (fun w => spinThetaChar d (-c) w tau) z := by
  have htau : tau ≠ 0 := ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt htauIm)
  let A : Complex := (-Complex.I * tau) ^ (1 / 2 : Complex)
  let F : Complex → Complex := fun w =>
    Complex.exp (Real.pi * Complex.I * w ^ 2 / tau + 2 * Real.pi * Complex.I * a * b)
  let G : Complex → Complex := fun w =>
    Complex.exp (Real.pi * Complex.I * w ^ 2 / tau + 2 * Real.pi * Complex.I * c * d)
  let f : Complex → Complex := fun w => spinThetaChar b (-a) w tau
  let g : Complex → Complex := fun w => spinThetaChar d (-c) w tau
  have hfunF : (fun w => spinThetaChar a b (w / tau) (-1 / tau)) =
      fun w => A * (F w * f w) := by
    funext w
    simpa [A, F, f, mul_assoc] using spinThetaChar_S a b w tau htau
  have hfunG : (fun w => spinThetaChar c d (w / tau) (-1 / tau)) =
      fun w => A * (G w * g w) := by
    funext w
    simpa [A, G, g, mul_assoc] using spinThetaChar_S c d w tau htau
  change thetaCross
        (fun w => spinThetaChar a b (w / tau) (-1 / tau))
        (fun w => spinThetaChar c d (w / tau) (-1 / tau)) z =
      A ^ 2 * Complex.exp (2 * (Real.pi * Complex.I * z ^ 2 / tau) +
        2 * Real.pi * Complex.I * (a * b + c * d)) * thetaCross f g z
  rw [thetaCross, hfunF, hfunG]
  have hF : DifferentiableAt Complex F z := by
    dsimp [F]
    fun_prop
  have hG : DifferentiableAt Complex G z := by
    dsimp [G]
    fun_prop
  have hf : DifferentiableAt Complex f z := by
    dsimp [f, spinThetaChar]
    have hj := (hasDerivAt_jacobiTheta₂_fst (z + b * tau + -a) htauIm).differentiableAt
    fun_prop
  have hg : DifferentiableAt Complex g z := by
    dsimp [g, spinThetaChar]
    have hj := (hasDerivAt_jacobiTheta₂_fst (z + d * tau + -c) htauIm).differentiableAt
    fun_prop
  rw [congrFun hfunG z, congrFun hfunF z]
  rw [deriv_const_mul_field, deriv_fun_mul hF hf, deriv_const_mul_field,
    deriv_fun_mul hG hg]
  have hFG : _root_.deriv F z * G z = _root_.deriv G z * F z := by
    dsimp [F, G]
    rw [deriv_cexp (by fun_prop), deriv_cexp (by fun_prop)]
    rw [deriv_add_const, deriv_add_const]
    ring
  have hprod : F z * G z =
      Complex.exp (2 * (Real.pi * Complex.I * z ^ 2 / tau) +
        2 * Real.pi * Complex.I * (a * b + c * d)) := by
    dsimp [F, G]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [thetaCross, ← hprod]
  ring_nf at hFG ⊢
  linear_combination A ^ 2 * f z * g z * hFG

end VOA
