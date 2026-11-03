import VOA.Classification.COne.QExpThetaSimpleZero
import VOA.Classification.COne.QExpThetaBoundary
import VOA.Classification.COne.QExpWeightOneReduction

/-!
# Intermediate comparison interfaces for the product route

`ThetaProductComparison` and `WeightOneLambertFourier` below are intermediate
interfaces. They are proved in `QExpThetaNontrivial` and `QExpThetaFourier`,
respectively. The former is the theta/product comparison up
to a nonzero scalar, as in DLMF 20.5.9 after shifting the elliptic variable.
The latter is the absolutely convergent Lambert-to-divisor regrouping for
Mascot's weight-one coefficients. The boundary term is retained.

References: https://dlmf.nist.gov/20.5.E9 and https://dlmf.nist.gov/20.5.E10.
The implications below separate the analytic and coefficient calculations.
Both interfaces are discharged downstream without adding assumptions.
-/

open Complex
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Residual comparison up to an unknown nonzero scalar, independent of `x`.
Proved by `thetaProductComparison` in `QExpThetaNontrivial`. -/
def ThetaProductComparison : Prop :=
  ∀ τ : ℍ, ∃ c : ℂ, c ≠ 0 ∧ ∀ x : ℂ,
    jacobiTheta₂ (x - ((τ : ℂ) + 1) / 2) τ = c * thetaShiftedProduct x τ

/-- The Fourier regrouping uses only explicit absolutely convergent sums.
Proved by `weightOneLambertFourier` in `QExpThetaFourier`.
In particular it has no theta function or modular slash action in its statement. -/
def WeightOneLambertFourier (N : ℕ) : Prop :=
  ∀ a b : Fin N, ¬(a.val = 0 ∧ b.val = 0) → ∀ τ : ℍ,
    let x := (a.val : ℂ) / N * τ + (b.val : ℂ) / N
    weightOneQSeries N (weightOneStandardRoot N) a b τ =
      weightOneScale N (weightOneStandardRoot N) a b *
        (1 / 2 - (a.val : ℂ) / N + thetaLambert (thetaExp τ) (thetaExp x) -
          thetaLambert (thetaExp τ) (thetaExp ((τ : ℂ) - x)))

/-- The original level range, without a change to the target's quantifiers. -/
def WeightOneLambertFourier24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → WeightOneLambertFourier N

/-- Torsion theta nonvanishing from only the residual product comparison. -/
theorem theta_torsion_ne_zero_of_productComparison (hp : ThetaProductComparison)
    {N : ℕ} (hN : 0 < N) (a b : Fin N) (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) :
    jacobiTheta₂ (((a.val : ℂ) / N - 1 / 2) * τ + ((b.val : ℂ) / N - 1 / 2)) τ ≠ 0 := by
  obtain ⟨c, hc, he⟩ := hp τ
  rw [show ((a.val : ℂ) / N - 1 / 2) * τ + ((b.val : ℂ) / N - 1 / 2) =
    ((a.val : ℂ) / N * τ + (b.val : ℂ) / N) - ((τ : ℂ) + 1) / 2 by ring, he]
  exact mul_ne_zero hc (thetaShiftedProduct_torsion_ne_zero hN a b hab τ)

/-- The scalar cancels from the logarithmic derivative; its value is never needed. -/
theorem thetaLog_eq_productLog_of_productComparison (hp : ThetaProductComparison)
    (τ : ℍ) (x : ℂ) :
    weightOneThetaLog (x - ((τ : ℂ) + 1) / 2) τ =
      _root_.deriv (fun y => thetaShiftedProduct y τ) x / thetaShiftedProduct x τ := by
  obtain ⟨c, hc, he⟩ := hp τ
  have hθ := (hasDerivAt_jacobiTheta₂_fst (x - ((τ : ℂ) + 1) / 2) τ.im_pos).comp x
    ((hasDerivAt_id x).sub_const (((τ : ℂ) + 1) / 2))
  have hP := ((thetaShiftedProduct_differentiable τ) x).hasDerivAt.const_mul c
  have hfun : (fun y => jacobiTheta₂ (y - ((τ : ℂ) + 1) / 2) τ) =
      (fun y => c * thetaShiftedProduct y τ) := funext he
  have hd : jacobiTheta₂' (x - ((τ : ℂ) + 1) / 2) τ =
      c * _root_.deriv (fun y => thetaShiftedProduct y τ) x := by
    apply HasDerivAt.unique (f := fun y => jacobiTheta₂ (y - ((τ : ℂ) + 1) / 2) τ)
    · simpa only [mul_one] using hθ
    · rw [hfun]
      exact hP
  rw [weightOneThetaLog, hd, he, mul_div_mul_left _ _ hc]

/-- Exact implication to the unchanged input. -/
theorem weightOneThetaFourier_of_productComparison_and_lambert
    (hp : ThetaProductComparison) {N : ℕ} (hN : 0 < N)
    (hf : WeightOneLambertFourier N) : WeightOneThetaFourier N := by
  intro a b hab τ
  refine ⟨theta_torsion_ne_zero_of_productComparison hp hN a b hab τ, ?_⟩
  have hv := thetaShiftedProduct_corrected_logDerivative hN a b hab τ
  dsimp only at hv
  have hz : ((a.val : ℂ) / N - 1 / 2) * τ + ((b.val : ℂ) / N - 1 / 2) =
      ((a.val : ℂ) / N * τ + (b.val : ℂ) / N) - ((τ : ℂ) + 1) / 2 := by ring
  rw [hf a b hab τ, weightOneThetaValue, hz,
    thetaLog_eq_productLog_of_productComparison hp, hv]

/-- Level-24 package, still conditional on the two explicit residual inputs. -/
theorem weightOneThetaFourier24_of_productComparison_and_lambert
    (hp : ThetaProductComparison) (hf : WeightOneLambertFourier24) : WeightOneThetaFourier24 :=
  fun N hN h24 => weightOneThetaFourier_of_productComparison_and_lambert hp hN (hf N hN h24)

theorem fullLevelWeightOneSlash24_of_productComparison_and_lambert
    (hp : ThetaProductComparison) (hf : WeightOneLambertFourier24) : FullLevelWeightOneSlash24 :=
  fullLevelWeightOneSlash24_of_thetaFourier
    (weightOneThetaFourier24_of_productComparison_and_lambert hp hf)

/-- This corollary still has analytic hypotheses; it is not the Sturm-only target. -/
theorem qExpPrinciple24Away_two_of_productComparison_lambert_and_sturmMatching
    (hp : ThetaProductComparison) (hf : WeightOneLambertFourier24)
    (hmatch : FullLevelWeightTwoSturmMatching24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_thetaFourier_and_sturmMatching
    (weightOneThetaFourier24_of_productComparison_and_lambert hp hf) hmatch

end VOA.Classification.COne.SSHecke
