import VOA.Huang.NgSchauenburgDimensions
import VOA.Huang.NgSchauenburgGeneralized
import VOA.Huang.NgSchauenburgCenterLinear

/-! # The degree-one generalized rotation and the central twist

All diagrams use the chosen nonstrict duals. The formula is derived from
half-braiding naturality, then applied to the pinned center representation.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

theorem halfBraiding_unit (X : Center C) :
    (X.2.β (𝟙_ C)).hom = (ρ_ X.1).hom ≫ (λ_ X.1).inv := by
  simpa only [Center.comp_f, Center.braiding_hom_f, Center.rightUnitor_hom_f,
    Center.leftUnitor_inv_f] using congrArg Center.Hom.f (braiding_tensorUnit_right X)

/-- Sliding a half-braiding across a coevaluation, including the unitors. -/
theorem halfBraiding_coevaluation (X : Center C) (U : C) :
    (ρ_ X.1).inv ≫ X.1 ◁ η_ U Uᘁ ≫ (α_ X.1 U Uᘁ).inv ≫
      (X.2.β U).hom ▷ Uᘁ =
    (λ_ X.1).inv ≫ η_ U Uᘁ ▷ X.1 ≫ (α_ U Uᘁ X.1).hom ≫
      U ◁ (X.2.β Uᘁ).inv ≫ (α_ U X.1 Uᘁ).inv := by
  apply (cancel_mono ((α_ U X.1 Uᘁ).hom ≫ U ◁ (X.2.β Uᘁ).hom ≫
    (α_ U Uᘁ X.1).inv)).mp
  calc
    _ = (ρ_ X.1).inv ≫ X.1 ◁ η_ U Uᘁ ≫ (X.2.β (U ⊗ Uᘁ)).hom := by
      rw [X.2.monoidal]
      simp only [Category.assoc]
    _ = (λ_ X.1).inv ≫ η_ U Uᘁ ▷ X.1 := by
      rw [X.2.naturality, halfBraiding_unit]
      simp
    _ = _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The generalized rotation in degree one, in an explicit cup-cap form. -/
theorem generalizedRotation_zero_apply (P : Pivotal C) (X : Center C) (V : C)
    (f : X.1 ⟶ V) :
    generalizedRotation P X V 0 f =
      (ρ_ X.1).inv ≫ X.1 ◁ η_ Vᘁ (Vᘁ)ᘁ ≫ (α_ X.1 Vᘁ (Vᘁ)ᘁ).inv ≫
        (X.2.β Vᘁ).hom ▷ (Vᘁ)ᘁ ≫
        (Vᘁ ◁ f ≫ ε_ V Vᘁ) ▷ (Vᘁ)ᘁ ≫ (λ_ (Vᘁ)ᘁ).hom ≫ (P.j V).inv := by
  change 𝟙 X.1 ≫ centerRotation P X V (𝟙_ C) (𝟙 X.1 ≫ f ≫ (ρ_ V).inv) ≫
    (λ_ V).hom = _
  dsimp [centerRotation, homCongr, leftDuality, rightDuality,
    tensorLeftHomEquiv, tensorRightHomEquiv]
  monoidal

@[reassoc]
theorem halfBraiding_inv_naturality (X : Center C) {U V : C} (f : U ⟶ V) :
    (X.2.β U).inv ≫ X.1 ◁ f = f ▷ X.1 ≫ (X.2.β V).inv := by
  apply (cancel_epi (X.2.β U).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← X.2.naturality_assoc]
  simp

/-- The central Drinfeld diagram followed by the double mate of an arbitrary
underlying morphism. No centrality condition on that morphism is required. -/
theorem centralDrinfeld_comp_doubleMate (X : Center C) {V : C} (f : X.1 ⟶ V) :
    centralDrinfeldMorphism X ≫ (fᘁ)ᘁ =
      (λ_ X.1).inv ≫ η_ Vᘁ (Vᘁ)ᘁ ▷ X.1 ≫ (α_ Vᘁ (Vᘁ)ᘁ X.1).hom ≫
        Vᘁ ◁ (X.2.β (Vᘁ)ᘁ).inv ≫ (α_ Vᘁ X.1 (Vᘁ)ᘁ).inv ≫
        (Vᘁ ◁ f ≫ ε_ V Vᘁ) ▷ (Vᘁ)ᘁ ≫ (λ_ (Vᘁ)ᘁ).hom := by
  calc
    _ = (λ_ X.1).inv ≫
        (η_ X.1ᘁ (X.1ᘁ)ᘁ ≫ X.1ᘁ ◁ (fᘁ)ᘁ) ▷ X.1 ≫
        (α_ X.1ᘁ (Vᘁ)ᘁ X.1).hom ≫ X.1ᘁ ◁ (X.2.β (Vᘁ)ᘁ).inv ≫
        (α_ X.1ᘁ X.1 (Vᘁ)ᘁ).inv ≫ ε_ X.1 X.1ᘁ ▷ (Vᘁ)ᘁ ≫
        (λ_ (Vᘁ)ᘁ).hom := by
      dsimp [centralDrinfeldMorphism]
      simp only [Category.assoc]
      rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
        ← associator_inv_naturality_right_assoc, ← whiskerLeft_comp_assoc,
        halfBraiding_inv_naturality, whiskerLeft_comp]
      monoidal
    _ = _ := by
      rw [coevaluation_comp_rightAdjointMate]
      have he := rightAdjointMate_comp_evaluation f
      simp only [comp_whiskerRight, Category.assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, he]
      simp

/-- The degree-one rotation is the inverse central twist on its source. -/
theorem generalizedRotation_one_centralDrinfeld (P : Pivotal C) (X : Center C) (V : C)
    (f : X.1 ⟶ V) :
    generalizedRotation P X V 0 f = centralDrinfeldMorphism X ≫ (P.j X.1).inv ≫ f := by
  rw [generalizedRotation_zero_apply]
  calc
    _ = (centralDrinfeldMorphism X ≫ (fᘁ)ᘁ) ≫ (P.j V).inv := by
      rw [centralDrinfeld_comp_doubleMate]
      rw [← reassoc_of% (halfBraiding_coevaluation X Vᘁ)]
      simp only [Category.assoc]
    _ = _ := by
      have hn : (fᘁ)ᘁ ≫ (P.j V).inv = (P.j X.1).inv ≫ f := by
        apply (cancel_epi (P.j X.1).hom).mp
        rw [← Category.assoc, ← P.naturality]
        simp
      rw [Category.assoc, hn]

/-- A pinned central twist eigenvalue determines the actual single rotation. -/
theorem generalizedRotation_one_scalar (P : Pivotal C) (X : Center C) (V : C)
    {t : ℂ} (ht : t ≠ 0)
    (hj : (P.j X.1).hom = t • centralDrinfeldMorphism X) (f : X.1 ⟶ V) :
    generalizedRotation P X V 0 f = t⁻¹ • f := by
  have hu : centralDrinfeldMorphism X ≫ (P.j X.1).inv = t⁻¹ • 𝟙 X.1 := by
    have hh : t • (centralDrinfeldMorphism X ≫ (P.j X.1).inv) = 𝟙 X.1 := by
      rw [← Linear.smul_comp, ← hj, Iso.hom_inv_id]
    rw [← hh, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [generalizedRotation_one_centralDrinfeld, ← Category.assoc, hu]
  simp

/-- Degree-one generalized indicators, including negative integer powers. -/
theorem generalizedIndicatorInt_one_scalar (F : SphericalFusion C) (X : Center C) (V : C)
    {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j X.1).hom = t • centralDrinfeldMorphism X) (l : ℤ) :
    generalizedIndicatorInt F.toPivotal X V 0 l =
      t ^ (-l) * (Module.finrank ℂ (X.1 ⟶ V) : ℂ) := by
  letI := F.homFinite X.1 V
  let tU : ℂˣ := Units.mk0 t ht
  have he : generalizedRotation F.toPivotal X V 0 =
      DistribMulAction.toLinearEquiv ℂ (X.1 ⟶ V) tU⁻¹ := by
    ext f
    exact generalizedRotation_one_scalar F.toPivotal X V ht hj f
  have hp : ((generalizedRotation F.toPivotal X V 0) ^ l).toLinearMap =
      t ^ (-l) • (1 : Module.End ℂ (X.1 ⟶ V)) := by
    rw [he]
    change ((DistribMulAction.toModuleAut ℂ (X.1 ⟶ V) tU⁻¹) ^ l).toLinearMap = _
    rw [← map_zpow]
    ext f
    simp [DistribMulAction.toModuleAut, DistribMulAction.toLinearEquiv, tU,
      Units.smul_def, zpow_neg]
  unfold generalizedIndicatorInt
  change LinearMap.trace ℂ (X.1 ⟶ V)
    (((generalizedRotation F.toPivotal X V 0) ^ l).toLinearMap) = _
  rw [hp]
  exact (LinearMap.trace ℂ (X.1 ⟶ V)).map_smul_of_tower (t ^ (-l)) 1 |>.trans
    (by rw [LinearMap.trace_one]; rfl)

section Center
variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]
open scoped MatrixGroups

/-- The `(1,l)` formula for the existing canonical-center normalization. -/
theorem generalizedIndicatorAll_one_twist (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (i : Z.Label) (l : ℤ) :
    generalizedIndicatorAll F (Z.simple i) V 1 l =
      M.twistScalar i ^ (-l) *
        (Module.finrank ℂ ((Z.simple i).1 ⟶ V) : ℂ) := by
  rw [show (1 : ℤ) = (0 : ℕ) + 1 by norm_num, generalizedIndicatorAll_positive]
  exact generalizedIndicatorInt_one_scalar F (Z.simple i) V
    (M.toRibbon.twistScalar_ne_zero i) (hr.2.1 i) l

/-- Actual T-generator equivariance on the entire first-index-one row. -/
theorem equivariantIndicator_one_T (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (l : ℤ) (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V 1 (l + 1) z =
      equivariantIndicator F Z.simple V 1 l (ρ ModularGroup.T⁻¹ z) := by
  have hi (i : Z.Label) : ρ ModularGroup.T⁻¹ z i = (M.twistScalar i)⁻¹ * z i := by
    have h := hr.2.2.2 (ρ ModularGroup.T⁻¹ z) i
    have hc : ρ ModularGroup.T (ρ ModularGroup.T⁻¹ z) = z := by
      rw [map_inv]; exact (ρ ModularGroup.T).apply_symm_apply z
    rw [hc] at h
    rw [h]
    simp [M.toRibbon.twistScalar_ne_zero i]
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk,
    generalizedIndicatorAll_one_twist F Z M ρ hr, hi]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_add, zpow_add₀ (M.toRibbon.twistScalar_ne_zero i)]
  simp only [zpow_neg_one]
  ring

end Center

end VOA.Huang.NgSchauenburg
