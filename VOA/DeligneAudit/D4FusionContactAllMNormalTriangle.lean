import VOA.DeligneAudit.D4FusionContactAllMNormalSeries
import VOA.DeligneAudit.D4FusionContactAllMNormalCoefficients

/-! Uniform higher triangle coefficient relations from whole source powers.
They include the static wheels and retain every mode-convolution term. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

def triangleCoeff (m k s : ℕ) : Poly m :=
  PowerSeries.coeff s (AllM.current m 0 ^ k * AllM.current m 1 *
    AllM.current m 2 * AllM.current m 3)

theorem simple_coeff_mem (m r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    PowerSeries.coeff s (AllM.current m 0 ^ r) ∈ AllM.candidateIdeal m :=
  AllM.seed_mem_candidate m ⟨(false, r, s), ⟨hr, hs⟩⟩

/-- A full coefficient relation, not its separate monomial summands.
The endpoint r>m includes the already proved static wheel family. -/
theorem triangleCoeff_mem (m k s : ℕ)
    (hs : m < k + 2 ∨ 2 * m ≤ (k + 2) + s) :
    triangleCoeff m k s ∈ AllM.candidateIdeal m := by
  let D₁ := g0Deriv m 7 0
  let D₂ := g0Deriv m 8 0
  let D₃ := g0Deriv m 9 0
  let U := AllM.current m 0
  let X := AllM.current m 1
  let Y := AllM.current m 2
  let Z := -AllM.current m 3
  let T := -AllM.current m 4
  have h₁ : seriesDeriv D₁ U = X := by
    apply PowerSeries.ext
    intro n
    simpa [D₁, U, X, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 0
  have h₂ : seriesDeriv D₂ U = Y := by
    apply PowerSeries.ext
    intro n
    simpa [D₂, U, Y, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 1
  have h₃ : seriesDeriv D₃ U = Z := by
    apply PowerSeries.ext
    intro n
    simpa [D₃, U, Z, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 2
  have h₂₁ : seriesDeriv D₂ X = T := by
    apply PowerSeries.ext
    intro n
    simpa [D₂, X, T, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 3
  have hregion (i j : ℕ) (hij : i + j = s) (hj : j < m) : m < k + 2 + i := by omega
  have hZ (j : ℕ) (hj : m ≤ j) : PowerSeries.coeff j Z = 0 := by
    simp only [Z, AllM.current, map_neg, PowerSeries.coeff_mk]
    rw [modeX, dif_neg (by omega), neg_zero]
  have hT (j : ℕ) (hj : m ≤ j) : PowerSeries.coeff j T = 0 := by
    simp only [T, AllM.current, map_neg, PowerSeries.coeff_mk]
    rw [modeX, dif_neg (by omega), neg_zero]
  have hleft : PowerSeries.coeff s (Z * seriesDeriv D₂ (seriesDeriv D₁ (U ^ (k + 2)))) ∈
      AllM.candidateIdeal m := by
    apply coeff_mul_mem_region (AllM.candidateIdeal m) _ _ m s hZ
    intro i j hij hj
    simp only [coeff_seriesDeriv]
    exact g0_closed m 0 8 (g0_closed m 0 7
      (simple_coeff_mem m (k + 2) i (by omega) (hregion i j hij hj)))
  have hright : PowerSeries.coeff s (T * seriesDeriv D₃ (U ^ (k + 2))) ∈
      AllM.candidateIdeal m := by
    apply coeff_mul_mem_region (AllM.candidateIdeal m) _ _ m s hT
    intro i j hij hj
    simp only [coeff_seriesDeriv]
    exact g0_closed m 0 9 (simple_coeff_mem m (k + 2) i (by omega) (hregion i j hij hj))
  have hrow : PowerSeries.coeff s
      (Z * seriesDeriv D₂ (seriesDeriv D₁ (U ^ (k + 2))) -
        T * seriesDeriv D₃ (U ^ (k + 2))) ∈ AllM.candidateIdeal m := by
    rw [map_sub]
    exact (AllM.candidateIdeal m).sub_mem hleft hright
  have he : Z * seriesDeriv D₂ (seriesDeriv D₁ (U ^ (k + 2))) -
      T * seriesDeriv D₃ (U ^ (k + 2)) =
      ((k + 2) * (k + 1) : ℕ) • (U ^ k * X * Y * Z) := by
    simpa only [nsmul_eq_mul] using AllMWheels.triangle_identity
      (seriesDeriv D₁) (seriesDeriv D₂) (seriesDeriv D₃) U X Y Z T h₁ h₂ h₃ h₂₁ k
  rw [he, map_nsmul] at hrow
  have hp : PowerSeries.coeff s (U ^ k * X * Y * Z) ∈ AllM.candidateIdeal m := by
    apply AllMWheels.cancel_nat_factor (AllM.candidateIdeal m) ((k + 2) * (k + 1))
      (by positivity)
    simpa only [nsmul_eq_mul] using hrow
  have hn : -triangleCoeff m k s ∈ AllM.candidateIdeal m := by
    simpa only [U, X, Y, Z, triangleCoeff, mul_neg, map_neg] using hp
  simpa only [neg_neg] using (AllM.candidateIdeal m).neg_mem hn

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.triangleCoeff_mem
