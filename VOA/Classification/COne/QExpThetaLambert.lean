import VOA.Classification.COne.QExpThetaLogDerivative

/-! # The explicit Lambert series of the shifted product -/

open Complex
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Lambert sum with its zeroth factor included. -/
def thetaLambert (r u : ℂ) : ℂ := ∑' n : ℕ, u * r ^ n / (1 - u * r ^ n)

theorem thetaLambert_summable {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    Summable (fun n : ℕ => u * r ^ n / (1 - u * r ^ n)) := by
  convert (thetaEulerProduct_log_summable hr u).mul_left (-u) using 1
  ext n
  ring

theorem thetaEulerProduct_factor_ne_one {r u : ℂ} (h : thetaEulerProduct r u ≠ 0)
    (n : ℕ) : u * r ^ n ≠ 1 := by
  intro hn
  apply h
  exact tprod_of_exists_eq_zero ⟨n, by rw [hn, sub_self]⟩

theorem thetaEulerProduct_parameter_logDerivative {r u : ℂ} (hr : ‖r‖ < 1)
    (hu : thetaEulerProduct r u ≠ 0) :
    u * (_root_.deriv (thetaEulerProduct r) u / thetaEulerProduct r u) = -thetaLambert r u := by
  rw [thetaEulerProduct_logDerivative hr (thetaEulerProduct_factor_ne_one hu),
    thetaLambert, ← tsum_mul_left, ← tsum_neg]
  apply tsum_congr
  intro n
  ring

theorem thetaExp_hasDerivAt (x : ℂ) :
    HasDerivAt thetaExp (2 * Real.pi * I * thetaExp x) x := by
  convert ((Complex.hasDerivAt_exp (2 * Real.pi * I * x)).comp x
    ((hasDerivAt_id x).const_mul (2 * Real.pi * I))) using 1
  simp only [thetaExp, one_mul, mul_comm]

/-- Logarithmic derivative of the product, with no theta-series hypothesis. -/
theorem thetaShiftedProduct_logDerivative (τ : ℍ) (x : ℂ)
    (hx : thetaShiftedProduct x τ ≠ 0) :
    _root_.deriv (fun y => thetaShiftedProduct y τ) x / thetaShiftedProduct x τ =
      (2 * Real.pi * I) *
        (thetaLambert (thetaExp τ) (thetaExp ((τ : ℂ) - x)) -
          thetaLambert (thetaExp τ) (thetaExp x)) := by
  have hr := thetaExp_norm_lt_one τ.im_pos
  obtain ⟨hu, hv⟩ := mul_ne_zero_iff.mp hx
  have hF := thetaEulerProduct_differentiable hr
  have hA := (hF (thetaExp x)).hasDerivAt.comp x (thetaExp_hasDerivAt x)
  have heB := (thetaExp_hasDerivAt ((τ : ℂ) - x)).comp x
    ((hasDerivAt_const x (τ : ℂ)).sub (hasDerivAt_id x))
  have hB := (hF (thetaExp ((τ : ℂ) - x))).hasDerivAt.comp x heB
  have hd := (hA.mul hB).deriv
  change _root_.deriv (fun y => thetaShiftedProduct y τ) x = _ at hd
  rw [hd]
  have hLA := thetaEulerProduct_parameter_logDerivative hr hu
  have hLB := thetaEulerProduct_parameter_logDerivative hr hv
  unfold thetaShiftedProduct
  dsimp only [Function.comp_apply] at *
  field_simp at hLA hLB ⊢
  linear_combination
    thetaEulerProduct (thetaExp τ) (thetaExp ((τ : ℂ) - x)) * hLA -
    thetaEulerProduct (thetaExp τ) (thetaExp x) * hLB

/-- Corrected logarithmic derivative, in a form ready for divisor regrouping. -/
theorem thetaShiftedProduct_corrected_logDerivative {N : ℕ} (hN : 0 < N)
    (a b : Fin N) (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) :
    let x := (a.val : ℂ) / N * τ + (b.val : ℂ) / N;
    -((a.val : ℂ) / N - 1 / 2) -
      (_root_.deriv (fun y => thetaShiftedProduct y τ) x / thetaShiftedProduct x τ) /
        (2 * Real.pi * I) =
      1 / 2 - (a.val : ℂ) / N + thetaLambert (thetaExp τ) (thetaExp x) -
        thetaLambert (thetaExp τ) (thetaExp ((τ : ℂ) - x)) := by
  dsimp only
  rw [thetaShiftedProduct_logDerivative τ _ (thetaShiftedProduct_torsion_ne_zero hN a b hab τ)]
  have hp : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [mul_div_cancel_left₀ _ hp]
  ring

end VOA.Classification.COne.SSHecke
