import VOA.Classification.COne.QExpThetaQuotient
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-! # Liouville's theorem for the extended theta/product quotient -/

open Complex Filter
open scoped Topology UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- A nonzero value of the product, used to invoke the identity principle. -/
theorem thetaShiftedProduct_half_ne_zero (τ : ℍ) : thetaShiftedProduct (1 / 2) τ ≠ 0 := by
  apply thetaShiftedProduct_ne_zero
  simpa using theta_unitSquare_not_lattice τ (α := 0) (β := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A shared nonzero multiplier becomes a period of the entire quotient.
The identity principle extends the equality across the product's zero lattice. -/
theorem thetaProductQuotient_periodic_of_multiplier (τ : ℍ) (p : ℂ) (A : ℂ → ℂ)
    (hA : ∀ x, A x ≠ 0)
    (hθ : ∀ x, jacobiTheta₂ ((x + p) - ((τ : ℂ) + 1) / 2) τ =
      A x * jacobiTheta₂ (x - ((τ : ℂ) + 1) / 2) τ)
    (hP : ∀ x, thetaShiftedProduct (x + p) τ = A x * thetaShiftedProduct x τ) :
    Function.Periodic (thetaProductQuotient τ) p := by
  have hQ := thetaProductQuotient_differentiable τ
  have hshift := hQ.comp (differentiable_id.add_const p)
  have he : (fun x => thetaProductQuotient τ (x + p)) = thetaProductQuotient τ := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (fun x _ => hshift.analyticAt x) (fun x _ => hQ.analyticAt x)
    filter_upwards [((thetaShiftedProduct_differentiable τ) (1 / 2)).continuousAt.eventually_ne
      (thetaShiftedProduct_half_ne_zero τ)] with x hx
    apply mul_right_cancel₀ hx
    apply mul_left_cancel₀ (hA x)
    have hh := thetaProductQuotient_mul τ (x + p)
    rw [hP, hθ, ← thetaProductQuotient_mul τ x] at hh
    dsimp only [Function.comp_apply, id_eq]
    convert hh using 1
    ring
  exact congrFun he

theorem thetaProductQuotient_period_one (τ : ℍ) :
    Function.Periodic (thetaProductQuotient τ) 1 := by
  apply thetaProductQuotient_periodic_of_multiplier τ 1 (fun _ => 1) (fun _ => one_ne_zero)
  · intro x
    rw [show (x + 1) - ((τ : ℂ) + 1) / 2 = (x - ((τ : ℂ) + 1) / 2) + 1 by ring,
      jacobiTheta₂_add_left, one_mul]
  · intro x
    rw [thetaShiftedProduct_add_one, one_mul]

theorem thetaProductQuotient_period_tau (τ : ℍ) :
    Function.Periodic (thetaProductQuotient τ) (τ : ℂ) := by
  apply thetaProductQuotient_periodic_of_multiplier τ τ (fun x => -(thetaExp x)⁻¹)
    (fun x => neg_ne_zero.mpr (inv_ne_zero (thetaExp_ne_zero x)))
  · intro x
    rw [show (x + τ) - ((τ : ℂ) + 1) / 2 = (x - ((τ : ℂ) + 1) / 2) + τ by ring,
      jacobiTheta₂_add_left']
    congr 1
    rw [show -Real.pi * I * ((τ : ℂ) + 2 * (x - ((τ : ℂ) + 1) / 2)) =
      Real.pi * I + -(2 * Real.pi * I * x) by ring,
      Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_neg]
    simp only [thetaExp, neg_mul, one_mul]
  · exact fun x => thetaShiftedProduct_add_tau x τ

/-- The real-linearly independent periods `1` and `τ`. -/
def thetaPeriodPair (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b he
    have hi := congrArg Complex.im he
    simp only [Complex.real_smul, mul_im, ofReal_re, ofReal_im, one_re, one_im,
      zero_im, zero_mul, mul_zero, zero_add, add_im, add_zero] at hi
    have hb : b = 0 := (mul_eq_zero.mp hi).resolve_right τ.im_pos.ne'
    subst b
    simpa using he

/-- The quotient is constant; no normalization of that constant is used. -/
theorem thetaProductQuotient_constant (τ : ℍ) (x y : ℂ) :
    thetaProductQuotient τ x = thetaProductQuotient τ y := by
  have hQ := thetaProductQuotient_differentiable τ
  apply hQ.apply_eq_apply_of_bounded
  apply (IsZLattice.isCompact_range_of_periodic (thetaPeriodPair τ).lattice _
    hQ.continuous ?_).isBounded
  intro z w hw
  obtain ⟨m, k, rfl⟩ := PeriodPair.mem_lattice.mp hw
  have h1 := (thetaProductQuotient_period_one τ).int_mul m
  have ht := (thetaProductQuotient_period_tau τ).int_mul k
  simpa only [thetaPeriodPair, mul_one] using h1.add_period ht z

/-- Unconditional proportionality, before proving the scalar is nonzero. -/
theorem theta_eq_scalar_mul_product (τ : ℍ) (x : ℂ) :
    jacobiTheta₂ (x - ((τ : ℂ) + 1) / 2) τ =
      thetaProductQuotient τ 0 * thetaShiftedProduct x τ := by
  rw [← thetaProductQuotient_mul, thetaProductQuotient_constant τ x 0]

/-- Remaining normalization input: theta is not identically zero at any upper-half-plane
parameter. Classically its integral over the real elliptic period is one (DLMF 20.2.3).
This interface is proved by `thetaSeriesNontrivial` in `QExpThetaNontrivial`. -/
def ThetaSeriesNontrivial : Prop :=
  ∀ τ : ℍ, ∃ z : ℂ, jacobiTheta₂ z τ ≠ 0

/-- The full nonzero comparison follows from only theta-series nontriviality. -/
theorem thetaProductComparison_of_nontrivial (hn : ThetaSeriesNontrivial) :
    ThetaProductComparison := by
  intro τ
  refine ⟨thetaProductQuotient τ 0, ?_, theta_eq_scalar_mul_product τ⟩
  obtain ⟨z, hz⟩ := hn τ
  intro hc
  have he := theta_eq_scalar_mul_product τ (z + ((τ : ℂ) + 1) / 2)
  rw [add_sub_cancel_right, hc, zero_mul] at he
  exact hz he

/-- Session-5 implication with the reduced residual input. -/
theorem weightOneThetaFourier_of_nontrivial_and_lambert (hn : ThetaSeriesNontrivial)
    {N : ℕ} (hN : 0 < N) (hf : WeightOneLambertFourier N) : WeightOneThetaFourier N :=
  weightOneThetaFourier_of_productComparison_and_lambert
    (thetaProductComparison_of_nontrivial hn) hN hf

theorem fullLevelWeightOneSlash24_of_nontrivial_and_lambert
    (hn : ThetaSeriesNontrivial) (hf : WeightOneLambertFourier24) : FullLevelWeightOneSlash24 :=
  fullLevelWeightOneSlash24_of_productComparison_and_lambert
    (thetaProductComparison_of_nontrivial hn) hf

theorem qExpPrinciple24Away_two_of_nontrivial_lambert_and_sturmMatching
    (hn : ThetaSeriesNontrivial) (hf : WeightOneLambertFourier24)
    (hmatch : FullLevelWeightTwoSturmMatching24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_productComparison_lambert_and_sturmMatching
    (thetaProductComparison_of_nontrivial hn) hf hmatch

end VOA.Classification.COne.SSHecke
