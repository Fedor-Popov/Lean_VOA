import VOA.Classification.COne.QExpThetaLiouville
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Theta has elliptic-period average one -/

open Complex MeasureTheory
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Every nonconstant elliptic Fourier mode has zero period integral. -/
theorem theta_term_period_integral (τ : ℂ) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x : ℂ) τ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn, jacobiTheta₂_term]
  · rw [if_neg hn]
    have hc : (2 * Real.pi * I * n : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (Int.cast_ne_zero.mpr hn)
    simp only [jacobiTheta₂_term, Complex.exp_add]
    rw [intervalIntegral.integral_mul_const, integral_exp_mul_complex hc]
    have he : cexp (2 * Real.pi * I * (n : ℂ)) = 1 := by
      rw [mul_comm _ (n : ℂ), Complex.exp_int_mul_two_pi_mul_I]
    simp [he]

/-- Interchanging theta's summation and the period integral is justified by
its summable Gaussian majorant, constant along the real elliptic period. -/
theorem theta_period_integral (τ : ℍ) :
    (∫ x in (0 : ℝ)..1, jacobiTheta₂ (x : ℂ) τ) = 1 := by
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 τ‖) :=
    ((summable_jacobiTheta₂_term_iff 0 τ).mpr τ.im_pos).norm
  have hn (n : ℤ) (x : ℝ) : ‖jacobiTheta₂_term n (x : ℂ) τ‖ =
      ‖jacobiTheta₂_term n 0 τ‖ := by simp [norm_jacobiTheta₂_term]
  have hi : HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x : ℂ) τ)
      (∫ x in (0 : ℝ)..1, jacobiTheta₂ (x : ℂ) τ) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => ‖jacobiTheta₂_term n 0 τ‖)
    · intro n
      have hc : Continuous (fun x : ℝ => jacobiTheta₂_term n (x : ℂ) τ) := by
        unfold jacobiTheta₂_term
        fun_prop
      exact hc.aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun x _ => (hn n x).le)
    · exact Filter.Eventually.of_forall (fun _ _ => hs)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun x _ => hasSum_jacobiTheta₂_term (x : ℂ) τ.im_pos)
  rw [← hi.tsum_eq]
  simp only [theta_term_period_integral]
  simp

/-- Theta cannot vanish identically: its period average is one. -/
theorem thetaSeriesNontrivial : ThetaSeriesNontrivial := by
  intro τ
  by_contra! hn
  have hi := theta_period_integral τ
  simp only [hn, intervalIntegral.integral_zero] at hi
  exact zero_ne_one hi

/-- Nonzero scalar comparison, proved without computing the triple-product constant. -/
theorem thetaProductComparison : ThetaProductComparison :=
  thetaProductComparison_of_nontrivial thetaSeriesNontrivial

/-- The required theta nonvanishing is unconditional, including `a=0`. -/
theorem theta_torsion_ne_zero {N : ℕ} (hN : 0 < N) (a b : Fin N)
    (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) :
    jacobiTheta₂ (((a.val : ℂ) / N - 1 / 2) * τ + ((b.val : ℂ) / N - 1 / 2)) τ ≠ 0 :=
  theta_torsion_ne_zero_of_productComparison thetaProductComparison hN a b hab τ

/-- Only the explicit Lambert-to-divisor regrouping remains in this implication. -/
theorem weightOneThetaFourier_of_lambert {N : ℕ} (hN : 0 < N)
    (hf : WeightOneLambertFourier N) : WeightOneThetaFourier N :=
  weightOneThetaFourier_of_productComparison_and_lambert thetaProductComparison hN hf

theorem fullLevelWeightOneSlash24_of_lambert (hf : WeightOneLambertFourier24) :
    FullLevelWeightOneSlash24 :=
  fullLevelWeightOneSlash24_of_productComparison_and_lambert thetaProductComparison hf

theorem qExpPrinciple24Away_two_of_lambert_and_sturmMatching
    (hf : WeightOneLambertFourier24) (hmatch : FullLevelWeightTwoSturmMatching24) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_productComparison_lambert_and_sturmMatching
    thetaProductComparison hf hmatch

end VOA.Classification.COne.SSHecke
