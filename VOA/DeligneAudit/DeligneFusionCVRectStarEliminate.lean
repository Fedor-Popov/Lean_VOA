import VOA.DeligneAudit.DeligneFusionCVRectStarEliminateVariables
import VOA.DeligneAudit.DeligneFusionCVRectStarFamily
import VOA.DeligneAudit.DeligneFusionCVRectStarFactor
import VOA.DeligneAudit.DeligneFusionCVRectEliminate

/-!
# Actual zero-site quotient maps for the three-color star family

A zero xy-site kills the highest retained x and y variables. Projection
removes them and has exactly the smaller coefficient ideal as image.
Its section therefore induces a surjection in the upper-bound direction.
No dimension recurrence or projection-kernel statement is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectStarEliminate

open CVRectStarBase CVRectStarIdeal CVRectStarFactor CVRectStarFamily

noncomputable section

theorem projectXY_ideal (L N R : ℕ) (left right center : List ℕ) :
    Ideal.map (projectXY L N R).toRingHom (ideal (L + 1) (N + 1) R (0 :: left) right center) =
      ideal L N R left right center := by
  unfold ideal
  rw [coefficientIdeal3_map, projectXY_starX, projectXY_starY, projectXY_starZ,
    CVRectStarFactor.coefficientIdeal3_zero_left]

theorem last_x_mem (L N R : ℕ) (left right center : List ℕ) :
    MvPolynomial.X (Sum.inl (Fin.last L)) ∈
      ideal (L + 1) (N + 1) R (0 :: left) right center := by
  have h : PowerSeries.coeff 0
      (starX (L + 1) (N + 1) R ^ 1 * starY (L + 1) (N + 1) R ^ 0 *
        starZ (L + 1) (N + 1) R ^ 0) ∈
      ideal (L + 1) (N + 1) R (0 :: left) right center := by
    exact Ideal.subset_span ⟨1, 0, 0, 0, by rw [starOrder_zero_left]; omega, rfl⟩
  simpa only [pow_one, pow_zero, mul_one, coeff_zero_starX] using h

theorem last_y_mem (L N R : ℕ) (left right center : List ℕ) :
    MvPolynomial.X (Sum.inr (Sum.inl (Fin.last N))) ∈
      ideal (L + 1) (N + 1) R (0 :: left) right center := by
  have h : PowerSeries.coeff 0
      (starX (L + 1) (N + 1) R ^ 0 * starY (L + 1) (N + 1) R ^ 1 *
        starZ (L + 1) (N + 1) R ^ 0) ∈
      ideal (L + 1) (N + 1) R (0 :: left) right center := by
    exact Ideal.subset_span ⟨0, 1, 0, 0, by rw [starOrder_zero_left]; omega, rfl⟩
  simpa only [pow_one, pow_zero, one_mul, mul_one, coeff_zero_starY] using h

theorem sectionXY_project_quotient (L N R : ℕ) (J : Ideal (StarRing (L + 1) (N + 1) R))
    (hx : MvPolynomial.X (Sum.inl (Fin.last L)) ∈ J)
    (hy : MvPolynomial.X (Sum.inr (Sum.inl (Fin.last N))) ∈ J) :
    ((Ideal.Quotient.mkₐ ℂ J).comp (sectionXY L N R)).comp (projectXY L N R) =
      Ideal.Quotient.mkₐ ℂ J := by
  ext x
  cases x with
  | inl i =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [AlgHom.comp_apply, projectXY_X_x_last, map_zero,
          Ideal.Quotient.mkₐ_eq_mk] using (Ideal.Quotient.eq_zero_iff_mem.mpr hx).symm
      · simp
  | inr x =>
      cases x with
      | inl j =>
          refine Fin.lastCases ?_ (fun j => ?_) j
          · simpa only [AlgHom.comp_apply, projectXY_X_y_last, map_zero,
              Ideal.Quotient.mkₐ_eq_mk] using (Ideal.Quotient.eq_zero_iff_mem.mpr hy).symm
          · simp
      | inr k => simp

def zeroLeftModelMap (L N R : ℕ) (left right center : List ℕ) :
    Model L N R left right center →ₐ[ℂ] Model (L + 1) (N + 1) R (0 :: left) right center :=
  CVRectEliminate.quotientSectionMap (sectionXY L N R) (projectXY L N R) _ _
    (projectXY_surjective L N R) (projectXY_ideal L N R left right center)
    (sectionXY_project_quotient L N R _
      (last_x_mem L N R left right center) (last_y_mem L N R left right center))

theorem zeroLeftModelMap_surjective (L N R : ℕ) (left right center : List ℕ) :
    Function.Surjective (zeroLeftModelMap L N R left right center) :=
  CVRectEliminate.quotientSectionMap_surjective _ _ _ _ _ _ _

def zeroLeftLengthEquiv (left right center : List ℕ) :
    Model (left.length + 1) (left.length + right.length + center.length + 1) right.length
      (0 :: left) right center ≃ₗ[ℂ] Family (0 :: left) right center := by
  change Model (left.length + 1) (left.length + right.length + center.length + 1) right.length
      (0 :: left) right center ≃ₗ[ℂ]
    Model (left.length + 1) (left.length + 1 + right.length + center.length) right.length
      (0 :: left) right center
  rw [show left.length + 1 + right.length + center.length =
    left.length + right.length + center.length + 1 by omega]

/-- Smaller actual star family surjects onto the family with an added
zero-capacity xy-site; this is the upper-bound direction. -/
def zeroLeftMap (left right center : List ℕ) :
    Family left right center →ₗ[ℂ] Family (0 :: left) right center :=
  (zeroLeftLengthEquiv left right center).toLinearMap.comp
    (zeroLeftModelMap left.length (left.length + right.length + center.length) right.length
      left right center).toLinearMap

theorem zeroLeftMap_surjective (left right center : List ℕ) :
    Function.Surjective (zeroLeftMap left right center) :=
  (zeroLeftLengthEquiv left right center).surjective.comp
    (zeroLeftModelMap_surjective left.length (left.length + right.length + center.length)
      right.length left right center)

theorem left_zero_bound (left right center : List ℕ)
    [FiniteDimensional ℂ (Family left right center)] :
    FiniteDimensional ℂ (Family (0 :: left) right center) ∧
      Module.finrank ℂ (Family (0 :: left) right center) ≤
        Module.finrank ℂ (Family left right center) := by
  have hs := zeroLeftMap_surjective left right center
  exact ⟨Module.Finite.of_surjective _ hs, LinearMap.finrank_le_finrank_of_surjective hs⟩

end

end VOA.DeligneAudit.A2.CVRectStarEliminate

#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.projectXY_ideal
#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.zeroLeftMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectStarEliminate.left_zero_bound
