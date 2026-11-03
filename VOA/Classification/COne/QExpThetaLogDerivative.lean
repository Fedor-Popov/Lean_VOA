import VOA.Classification.COne.QExpThetaZeros

/-! # Logarithmic differentiation of the convergent Euler product -/

open Complex Filter
open scoped Topology UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Absolute convergence of the logarithmic derivative away from the factors' zeros. -/
theorem thetaEulerProduct_log_summable {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    Summable (fun n : ℕ => -(r ^ n) / (1 - u * r ^ n)) := by
  have hp : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
  have hd : Tendsto (fun n : ℕ => (1 - u * r ^ n)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)).inv₀
      (show (1 : ℂ) - u * 0 ≠ 0 by simp)
  have hb : ∀ᶠ n : ℕ in atTop, ‖(1 - u * r ^ n)⁻¹‖ ≤ 2 := by
    exact hd.norm.eventually_le_const (by norm_num)
  apply Summable.of_norm
  apply ((summable_geometric_of_lt_one (norm_nonneg r) hr).mul_right 2).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hb] with n hn
  simpa only [Real.norm_eq_abs, abs_norm, div_eq_mul_inv, norm_mul, norm_neg, norm_pow] using
    mul_le_mul_of_nonneg_left hn (pow_nonneg (norm_nonneg r) n)

/-- Finite-product logarithmic differentiation, with all denominators justified. -/
theorem thetaEulerProduct_partial_hasDerivAt (r u : ℂ)
    (hu : ∀ n : ℕ, u * r ^ n ≠ 1) (s : Finset ℕ) :
    HasDerivAt (fun v : ℂ => ∏ n ∈ s, (1 - v * r ^ n))
      ((∏ n ∈ s, (1 - u * r ^ n)) *
        ∑ n ∈ s, -(r ^ n) / (1 - u * r ^ n)) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const u (1 : ℂ)
  | @insert i s hi ih =>
    have hf : HasDerivAt (fun v : ℂ => 1 - v * r ^ i) (-(r ^ i)) u := by
      simpa using (hasDerivAt_const u (1 : ℂ)).sub ((hasDerivAt_id u).mul_const (r ^ i))
    convert hf.mul ih using 1
    · ext v
      simp [Finset.prod_insert, hi]
    · simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      have hn : 1 - u * r ^ i ≠ 0 := sub_ne_zero.mpr (Ne.symm (hu i))
      field_simp

/-- The derivative is the product times the absolutely convergent logarithmic sum. -/
theorem thetaEulerProduct_deriv {r u : ℂ} (hr : ‖r‖ < 1)
    (hu : ∀ n : ℕ, u * r ^ n ≠ 1) :
    _root_.deriv (thetaEulerProduct r) u = thetaEulerProduct r u *
      ∑' n : ℕ, -(r ^ n) / (1 - u * r ^ n) := by
  have hconv := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (thetaEulerProduct_hasProdLocallyUniformlyOn hr)
  have hdiff : ∀ᶠ s : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun v : ℂ => ∏ n ∈ s, (1 - v * r ^ n)) Set.univ :=
    Eventually.of_forall (fun s =>
      (Differentiable.fun_finsetProd (fun n _ =>
        (differentiable_const (1 : ℂ)).sub
          (differentiable_id.mul_const (r ^ n)))).differentiableOn)
  have hd := (hconv.deriv hdiff isOpen_univ).tendsto_at (Set.mem_univ u)
  have hl := Filter.Tendsto.mul (thetaEulerProduct_multipliable hr u).hasProd
    (thetaEulerProduct_log_summable hr u).hasSum
  apply tendsto_nhds_unique hd
  convert hl using 1
  ext s
  exact (thetaEulerProduct_partial_hasDerivAt r u hu s).deriv

/-- The unknown scalar multiplying a product cancels from its logarithmic derivative. -/
theorem thetaEulerProduct_logDerivative {r u : ℂ} (hr : ‖r‖ < 1)
    (hu : ∀ n : ℕ, u * r ^ n ≠ 1) :
    _root_.deriv (thetaEulerProduct r) u / thetaEulerProduct r u =
      ∑' n : ℕ, -(r ^ n) / (1 - u * r ^ n) := by
  rw [thetaEulerProduct_deriv hr hu, mul_div_cancel_left₀ _ (thetaEulerProduct_ne_zero hr hu)]

end VOA.Classification.COne.SSHecke
