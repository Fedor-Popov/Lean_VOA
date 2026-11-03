import VOA.DeligneAudit.DeligneFusionCVRectAdjointFamily
import VOA.DeligneAudit.DeligneFusionCVRectStarEliminate

/-! # Actual zero xy-site maps for arbitrary extra coefficient orders -/

namespace VOA.DeligneAudit.A2.CVRectAdjointEliminate

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarEliminate
open VOA.DeligneAudit.A2.CVRectAdjointFamily

noncomputable section

theorem projectXY_ideal (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Ideal.map (projectXY L N R).toRingHom
      (ideal (L + 1) (N + 1) R (fun p q r => μ p q r + p + q)) = ideal L N R μ := by
  unfold ideal
  rw [coefficientIdeal3_map, projectXY_starX, projectXY_starY, projectXY_starZ]
  simpa only [pow_one, pow_zero, one_mul, zero_mul, Nat.add_zero] using
    CVRectStarFactor.coefficientIdeal3_factor
      (starX L N R) (starY L N R) (starZ L N R) μ 1 1 0

theorem last_x_mem (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    MvPolynomial.X (Sum.inl (Fin.last L)) ∈
      ideal (L + 1) (N + 1) R (fun p q r => μ p q r + p + q) := by
  have h : PowerSeries.coeff 0
      (starX (L + 1) (N + 1) R ^ 1 * starY (L + 1) (N + 1) R ^ 0 *
        starZ (L + 1) (N + 1) R ^ 0) ∈
      ideal (L + 1) (N + 1) R (fun p q r => μ p q r + p + q) :=
    Ideal.subset_span ⟨1, 0, 0, 0, by change 0 < μ 1 0 0 + 1 + 0; omega, rfl⟩
  simpa only [pow_one, pow_zero, mul_one, coeff_zero_starX] using h

theorem last_y_mem (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    MvPolynomial.X (Sum.inr (Sum.inl (Fin.last N))) ∈
      ideal (L + 1) (N + 1) R (fun p q r => μ p q r + p + q) := by
  have h : PowerSeries.coeff 0
      (starX (L + 1) (N + 1) R ^ 0 * starY (L + 1) (N + 1) R ^ 1 *
        starZ (L + 1) (N + 1) R ^ 0) ∈
      ideal (L + 1) (N + 1) R (fun p q r => μ p q r + p + q) :=
    Ideal.subset_span ⟨0, 1, 0, 0, by change 0 < μ 0 1 0 + 0 + 1; omega, rfl⟩
  simpa only [pow_one, pow_zero, one_mul, mul_one, coeff_zero_starY] using h

/-- A zero xy-site is removed in the upper-bound direction for every
extra order function, including the adjoint and five-shape functions. -/
def zeroXYModelMap (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Model L N R μ →ₐ[ℂ] Model (L + 1) (N + 1) R (fun p q r => μ p q r + p + q) :=
  CVRectEliminate.quotientSectionMap (sectionXY L N R) (projectXY L N R) _ _
    (projectXY_surjective L N R) (projectXY_ideal L N R μ)
    (sectionXY_project_quotient L N R _ (last_x_mem L N R μ) (last_y_mem L N R μ))

theorem zeroXYModelMap_surjective (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Function.Surjective (zeroXYModelMap L N R μ) :=
  CVRectEliminate.quotientSectionMap_surjective _ _ _ _ _ _ _

theorem zeroXY_model_bound (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ)
    [FiniteDimensional ℂ (Model L N R μ)] :
    FiniteDimensional ℂ (Model (L + 1) (N + 1) R (fun p q r => μ p q r + p + q)) ∧
      Module.finrank ℂ (Model (L + 1) (N + 1) R (fun p q r => μ p q r + p + q)) ≤
        Module.finrank ℂ (Model L N R μ) := by
  let f := (zeroXYModelMap L N R μ).toLinearMap
  have hf : Function.Surjective f := zeroXYModelMap_surjective L N R μ
  exact ⟨Module.Finite.of_surjective f hf, LinearMap.finrank_le_finrank_of_surjective hf⟩

end
end VOA.DeligneAudit.A2.CVRectAdjointEliminate

#print axioms VOA.DeligneAudit.A2.CVRectAdjointEliminate.zeroXYModelMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectAdjointEliminate.zeroXY_model_bound
