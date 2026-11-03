import VOA.Huang.NgSchauenburgPrimitiveArithmetic

/-! # Primitive-row arithmetic applied to the actual mixed representation

The categorical hypotheses below are not proved in this module. The conclusion
uses the exact raw twist order and the actual mixed indicators, and requires
no fusion structure on the center and no nonprimitive orbit theorem.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits BraidedCategory
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- T has the raw categorical twist period in the actual mixed representation. -/
theorem mixedRepresentation_T_period (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    (mixedRepresentation ρ ModularGroup.T) ^ M.toRibbon.twistOrder = 1 := by
  have h : matrixDouble (matrixLinearEquiv.symm (ρ ModularGroup.T)) ^
      M.toRibbon.twistOrder = 1 := by
    rw [mixedRepresentation_T_matrix F M ρ hr, ← mixedT_orderOf F M.toRibbon]
    exact pow_orderOf_eq_one _
  apply matrixLinearEquiv.symm.injective
  apply Units.ext
  change (matrixLinearEquiv.symm ((mixedRepresentation ρ ModularGroup.T) ^
    M.toRibbon.twistOrder) : Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ) = _
  rw [map_pow, map_one]
  have hd : matrixLinearEquiv.symm (mixedRepresentation ρ ModularGroup.T) =
      matrixDouble.toHomUnits (matrixLinearEquiv.symm (ρ ModularGroup.T)) := by
    simp [mixedRepresentation]
  rw [hd, Units.val_pow_eq_pow_val]
  exact h

open Classical in
/-- The primitive rescaling step suffices for projective congruence, once
equivariance of the actual mixed indicators is supplied. -/
theorem projectiveCongruence_of_mixed_primitive_rescaling
    (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ)
    (he : ∀ (a : F.Label) (m l : ℤ) (γ : SL(2, ℤ)) (z : F.Label × F.Label → ℂ),
      equivariantIndicator F
        (fun p : F.Label × F.Label => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) (rowAction m l γ).1 (rowAction m l γ).2 z =
      equivariantIndicator F
        (fun p : F.Label × F.Label => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) m l (mixedRepresentation ρ (modularInvolution γ) z))
    (hscale : ∀ (a : F.Label) (r s : ℤ), IsCoprime r s →
      Int.ModEq M.toRibbon.twistOrder r 1 → ∀ (i j : F.Label),
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
        (F.simple a) s (-r) =
      generalizedIndicatorAll F (mixedCenter (F.simple i) (F.simple j))
        (F.simple a) s (-1)) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder := by
  apply projectiveCongruence_of_mixed_invariance F M ρ hr
  intro γ hγ a z
  refine one_zero_invariant_of_primitive_rescaling (mixedRepresentation ρ)
    (fun m l w => equivariantIndicator F
      (fun p : F.Label × F.Label => mixedCenter (F.simple p.1) (F.simple p.2)) (F.simple a) m l w)
    M.toRibbon.twistOrder (he a) (mixedRepresentation_T_period F M ρ hr)
    ?_ γ hγ z
  intro r s hrs hrN w
  have hmod : Int.ModEq M.toRibbon.twistOrder r 1 :=
    (ZMod.intCast_eq_intCast_iff r 1 _).mp (by simpa using hrN)
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    hscale a r s hrs hmod]

end VOA.Huang.NgSchauenburg
