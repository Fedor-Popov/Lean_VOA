import VOA.Huang.GenusOneQEquationSepWardSystem
import VOA.Huang.GenusOneQEquationSepScalar
import VOA.Huang.GenusTwoPointSepCuspTrace

/-!
# Outer two-point q-convergence from the evaluated Ward system

The named residual concerns the actual geometrically modified trace series,
whose spatial coefficients have already been summed by genus-zero convergence.
C₂-cofiniteness of both insertions is discharged by Buhl. No intermediate-level
bound, exchange of infinite sums, or separate-Fuchsian hypothesis is used.

This file proves a conditional ProductQSummable result. It does not prove the
Ward residual, joint double-series convergence, or modular invariance.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation FuchsianODE
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The two algebraic Ward consequences still needed after spatial evaluation.
The first is the consequence of both collected minus-two identities. The second
expresses energy insertion in the span of insertion descendants, including the
spatial terms in Huang's mixed operator. Coefficients are regular on the chosen
rescaled q-disc. This is a sufficient residual, not a claim of its existence or
an identification of the coefficient ring with Huang's four-generator ring. -/
def ProductCuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) : Prop :=
  C2Reduction (R := ↥SubexpPS) P₁.isMod.toWeakModule P₂.isMod.toWeakModule
    (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho) ∧
  PairEulerClosed SubexpPS (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (N.h - W.centralCharge / 24)

/-- The original collected Ward predicates imply the reduction part of the
new residual. Energy closure remains an independent explicit hypothesis. -/
theorem productCuspWard_of_collected (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (c : Kernels ↥SubexpPS)
    (hL : CollectedLeftWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c
      (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho))
    (hR : CollectedRightWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c
      (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho))
    (hD : PairEulerClosed SubexpPS (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
      (N.h - W.centralCharge / 24)) :
    ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho :=
  ⟨c2Reduction_of_collected _ _ c _ hL hR, hD⟩

/-- The actual modified traces belong to a finite regular-singular q-system,
conditional on the two evaluated Ward consequences. Module C₂ is proved. -/
theorem exists_product_cusp_system (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho) :
    ∃ (U : Finset P₁.carrier) (Z : Finset P₂.carrier)
      (C : U × Z → U × Z → ↥SubexpPS),
      (∀ k, thetaShift (N.h - W.centralCharge / 24)
          (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho k.1.val k.2.val) =
        ∑ l : U × Z, (C k l).val *
          modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho l.1.val l.2.val) ∧
      (∀ x y, ∃ c : U × Z → ↥SubexpPS,
        modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y =
        ∑ l : U × Z, (c l).val *
          modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho l.1.val l.2.val) := by
  obtain ⟨U, Z, hUZ⟩ := exists_pair_euler_system SubexpPS
    P₁.isMod.toAdmissible P₂.isMod.toAdmissible
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₁)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₂)
  obtain ⟨C, hC, hgen⟩ := hUZ _ _ hward.1 hward.2
  exact ⟨U, Z, C, hC, hgen⟩

/-- Raw traces inherit convergence by the actual inverse coordinate operators;
no infinite insertion vector or raw/modified differential equation is assumed. -/
theorem productCuspSeries_mem_subexp (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (x : P₁.carrier) (y : P₂.carrier) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y ∈ SubexpPS := by
  rw [← modifiedProductCuspSeries_inverse hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y]
  exact pairSeries_mem_subexp_of_C2 SubexpPS le_rfl
    P₁.isMod.toAdmissible P₂.isMod.toAdmissible
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₁)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₂)
    _ _ hward.1 hward.2 _ _

/-- Absolute convergence of the normalized outer series on its q-disc. -/
theorem summable_product_qPowers_of_cuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (q : ℂ) (hq : ‖q‖ < ‖rho‖) :
    Summable (fun n : ℕ => ‖productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ * q ^ n‖) := by
  have hr : rho ≠ 0 := by
    intro hr
    rw [hr, norm_zero] at hq
    exact (norm_nonneg _).not_gt hq
  have hqr : ‖q / rho‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hr)]
    exact hq
  have hsub := productCuspSeries_mem_subexp hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho hward x y
  have hs := summable_of_subexponential
    (fun n => norm_nonneg (PowerSeries.coeff n
      (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y))) hsub
    (norm_nonneg (q / rho)) hqr
  have hs' : Summable (fun n => PowerSeries.coeff n
      (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) * (q / rho) ^ n) :=
    (by simpa only [norm_mul, norm_pow] using hs : Summable (fun n =>
      ‖PowerSeries.coeff n (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) *
        (q / rho) ^ n‖)).of_norm
  have heq (n : ℕ) : PowerSeries.coeff n
      (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) * (q / rho) ^ n =
      productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ * q ^ n := by
    rw [coeff_productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hx hy, div_pow]
    field_simp
  exact (hs'.congr heq).norm

/-- The finite regular q-system discharges exactly ProductQSummable at q/rho.
The inner spatial sum was certified before the q-ODE argument. -/
theorem productQSummable_of_cuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ < ‖rho‖) :
    ProductQSummable Y₁ Y₂ x y α₁ α₂ z₁ z₂ τ := by
  have hs := summable_product_qPowers_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    hward (qParam τ) hq
  have ht := hs.of_norm.mul_right
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) *
      (N.h - W.centralCharge / 24)))
  exact ht.congr (fun n => by dsimp [qFactor]; ring)

/-- The normalized actual trace is analytic at the q-cusp. The possibly
fractional conformal prefactor is excluded from this analytic-at-zero claim. -/
theorem analyticAt_product_qSeries_zero_of_cuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (hrho : rho ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ => ∑' n : ℕ,
      productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ * q ^ n) 0 := by
  have hr : 0 < ‖rho‖ / 2 := half_pos (norm_pos_iff.mpr hrho)
  apply analyticAt_zero_of_summable _ (‖rho‖ / 2) hr
  have hs := summable_product_qPowers_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    hward ((‖rho‖ / 2 : ℝ) : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      linarith [norm_pos_iff.mpr hrho])
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hs

/-- Ward identities on each smaller q-disc give outer convergence throughout
the product annulus. This still asserts outer convergence only. -/
theorem productQSummable_in_annulus_of_cuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (hward : ∀ r : ℝ, 0 < r → r < ‖z₂‖ / ‖z₁‖ →
      ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (r : ℂ))
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductQSummable Y₁ Y₂ x y α₁ α₂ z₁ z₂ τ := by
  have hz₁ : 0 < ‖z₁‖ := (norm_nonneg z₂).trans_lt hz
  obtain ⟨r, hqr, hr⟩ := exists_between ((lt_div_iff₀ hz₁).mpr hq)
  have hr₀ : 0 < r := (norm_nonneg (qParam τ)).trans_lt hqr
  apply productQSummable_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    (hward r hr₀ hr) τ
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀] using hqr

/-- Certified value of the actual outer q-trace under the same Ward input. -/
theorem hasSum_product_qTrace_of_cuspWard (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hward : ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ < ‖rho‖) :
    HasSum (fun n : ℕ => productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ * qFactor N τ n)
      (qTrace N (fun β => productCoeff Y₁ Y₂ x y α₁ α₂ β z₁ z₂) τ) :=
  (productQSummable_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz hward τ hq).hasSum

end VOA.Huang.GenusTwoPoint.Separate
