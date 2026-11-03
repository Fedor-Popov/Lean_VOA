import VOA.DeligneAudit.D4FusionContactAllMNormalOpposite

/-! The symmetric higher triangle family, with opposite coefficients proved. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

noncomputable section

def backTriangleCoeff (m k s : ℕ) : Poly m :=
  PowerSeries.coeff s (AllM.current m 7 ^ k * AllM.current m 4 *
    AllM.current m 5 * AllM.current m 6)

theorem backTriangleCoeff_mem (m k s : ℕ)
    (hs : m < k + 2 ∨ 2 * m ≤ (k + 2) + s) :
    backTriangleCoeff m k s ∈ AllM.candidateIdeal m := by
  let D₁ := g0Deriv m 4 0
  let D₂ := g0Deriv m 5 0
  let D₃ := g0Deriv m 6 0
  let U := AllM.current m 7
  let X := -AllM.current m 6
  let Y := -AllM.current m 5
  let Z := AllM.current m 4
  let T := AllM.current m 3
  have h₁ : seriesDeriv D₁ U = X := by
    apply PowerSeries.ext
    intro n
    simpa [D₁, U, X, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 8
  have h₂ : seriesDeriv D₂ U = Y := by
    apply PowerSeries.ext
    intro n
    simpa [D₂, U, Y, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 9
  have h₃ : seriesDeriv D₃ U = Z := by
    apply PowerSeries.ext
    intro n
    simpa [D₃, U, Z, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 10
  have hraw : seriesDeriv D₂ (AllM.current m 6) = -T := by
    apply PowerSeries.ext
    intro n
    simpa [D₂, T, AllM.current, AllMWheels.direction, AllMWheels.sourceColor,
      AllMWheels.targetColor, AllMWheels.actionCoeff] using action_mode m n 11
  have h₂₁ : seriesDeriv D₂ X = T := by
    change seriesDeriv D₂ (-AllM.current m 6) = T
    rw [map_neg, hraw, neg_neg]
  have hregion (i j : ℕ) (hij : i + j = s) (hj : j < m) : m < k + 2 + i := by omega
  have hZ (j : ℕ) (hj : m ≤ j) : PowerSeries.coeff j Z = 0 := by
    simp only [Z, AllM.current, PowerSeries.coeff_mk]
    exact dif_neg (by omega)
  have hT (j : ℕ) (hj : m ≤ j) : PowerSeries.coeff j T = 0 := by
    simp only [T, AllM.current, PowerSeries.coeff_mk]
    exact dif_neg (by omega)
  have hleft : PowerSeries.coeff s (Z * seriesDeriv D₂ (seriesDeriv D₁ (U ^ (k + 2)))) ∈
      AllM.candidateIdeal m := by
    apply coeff_mul_mem_region (AllM.candidateIdeal m) _ _ m s hZ
    intro i j hij hj
    simp only [coeff_seriesDeriv]
    exact g0_closed m 0 5 (g0_closed m 0 4
      (opposite_power_coeff_mem m (k + 2) i (by omega) (hregion i j hij hj)))
  have hright : PowerSeries.coeff s (T * seriesDeriv D₃ (U ^ (k + 2))) ∈
      AllM.candidateIdeal m := by
    apply coeff_mul_mem_region (AllM.candidateIdeal m) _ _ m s hT
    intro i j hij hj
    simp only [coeff_seriesDeriv]
    exact g0_closed m 0 6 (opposite_power_coeff_mem m (k + 2) i (by omega) (hregion i j hij hj))
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
  have heq : U ^ k * X * Y * Z =
      AllM.current m 7 ^ k * AllM.current m 4 * AllM.current m 5 * AllM.current m 6 := by
    dsimp only [U, X, Y, Z]
    ring
  simpa only [heq, backTriangleCoeff] using hp

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.backTriangleCoeff_mem
