import VOA.Huang.NgSchauenburgPartialTrace

/-! # Fusion of half-braiding loops

The individual loops define an action of the fusion algebra on underlying Hom
spaces. All statements use the actual cup-cap diagrams.
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

/-- Naturality of the open conjugation diagram in its loop label. -/
theorem halfBraidingConjugation_naturality (X Y : Center C) (f : X.1 ⟶ Y.1)
    {U V : C} (a : U ⟶ V) :
    a ▷ X.1 ≫ ((X.2.β V).inv ≫ f ▷ V ≫ (Y.2.β V).hom) =
      ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom) ≫ a ▷ Y.1 := by
  have hi : a ▷ X.1 ≫ (X.2.β V).inv = (X.2.β U).inv ≫ X.1 ◁ a := by
    apply (cancel_epi (X.2.β U).hom).mp
    rw [← X.2.naturality_assoc]
    simp
  rw [← Category.assoc (a ▷ X.1), hi]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, Y.2.naturality]

/-- The loop depends only on the isomorphism class of its label. -/
theorem halfBraidingLoop_iso (F : SphericalFusion C) (X Y : Center C)
    {U V : C} (e : U ≅ V) :
    halfBraidingLoop F.toPivotal X Y U = halfBraidingLoop F.toPivotal X Y V := by
  apply LinearMap.ext
  intro f
  have h := F.partialTraceLeft_iso e
    ((X.2.β V).inv ≫ f ▷ V ≫ (Y.2.β V).hom)
  rw [← Category.assoc, halfBraidingConjugation_naturality] at h
  simpa only [Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.comp_id] using h

/-- Resolve an arbitrary loop label into its actual simple multiplicities. -/
theorem halfBraidingLoop_eq_sum_simples (F : SphericalFusion C)
    (X Y : Center C) (U : C) :
    halfBraidingLoop F.toPivotal X Y U =
      ∑ i, (Module.finrank ℂ (F.simple i ⟶ U) : ℂ) •
        halfBraidingLoop F.toPivotal X Y (F.simple i) := by
  classical
  apply LinearMap.ext
  intro f
  change F.toPivotal.partialTraceLeft U _ = _
  rw [F.partialTraceLeft_eq_sum_channels]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin (Module.finrank ℂ (F.simple i ⟶ U))) :
      F.simpleHomBasis U i a ▷ X.1 ≫
        ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom) ≫
        F.compositionDual (F.simpleHomBasis U i) a ▷ Y.1 =
      (X.2.β (F.simple i)).inv ≫ f ▷ F.simple i ≫ (Y.2.β (F.simple i)).hom := by
    rw [← Category.assoc, halfBraidingConjugation_naturality]
    simp [← comp_whiskerRight, F.basis_comp_compositionDual]
  simp only [he]
  simp [halfBraidingLoop, ← Nat.cast_smul_eq_nsmul ℂ]

/-- Tensoring loop labels composes their actions, in the traced order. -/
theorem halfBraidingLoop_tensor (F : SphericalFusion C) (X Y : Center C) (U V : C) :
    halfBraidingLoop F.toPivotal X Y (U ⊗ V) =
      (halfBraidingLoop F.toPivotal X Y V).comp
        (halfBraidingLoop F.toPivotal X Y U) := by
  apply LinearMap.ext
  intro f
  change F.toPivotal.partialTraceLeft (U ⊗ V) _ = _
  rw [F.partialTraceLeft_tensor]
  have hx : (X.2.β (U ⊗ V)).inv =
      (α_ U V X.1).hom ≫ U ◁ (X.2.β V).inv ≫ (α_ U X.1 V).inv ≫
        (X.2.β U).inv ▷ V ≫ (α_ X.1 U V).hom := by
    apply (cancel_epi (X.2.β (U ⊗ V)).hom).mp
    rw [Iso.hom_inv_id, X.2.monoidal]
    simp
  rw [hx, Y.2.monoidal]
  have he : (α_ U V X.1).inv ≫
      ((α_ U V X.1).hom ≫ U ◁ (X.2.β V).inv ≫ (α_ U X.1 V).inv ≫
        (X.2.β U).inv ▷ V ≫ (α_ X.1 U V).hom) ≫
      f ▷ (U ⊗ V) ≫
      ((α_ Y.1 U V).inv ≫ (Y.2.β U).hom ▷ V ≫ (α_ U Y.1 V).hom ≫
        U ◁ (Y.2.β V).hom ≫ (α_ U V Y.1).inv) ≫ (α_ U V Y.1).hom =
      U ◁ (X.2.β V).inv ≫
        ((α_ U X.1 V).inv ≫
          ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom) ▷ V ≫
            (α_ U Y.1 V).hom) ≫ U ◁ (Y.2.β V).hom := by
    monoidal
  simp only [Category.assoc] at he ⊢
  rw [he, F.toPivotal.partialTraceLeft_precomp]
  have hp := F.toPivotal.partialTraceLeft_postcomp U
    ((α_ U X.1 V).inv ≫
      ((X.2.β U).inv ≫ f ▷ U ≫ (Y.2.β U).hom) ▷ V ≫ (α_ U Y.1 V).hom)
    (Y.2.β V).hom
  simp only [Category.assoc] at hp
  rw [hp, F.toPivotal.partialTraceLeft_whisker]
  rfl

end VOA.Huang.NgSchauenburg
