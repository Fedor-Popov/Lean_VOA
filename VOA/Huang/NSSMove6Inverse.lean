import VOA.Huang.NSSMove6Crossing

/-! # Sewing the first label of the inverse mixed crossing -/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Bend the last factor of a morphism, retaining the pivotal identification. -/
def rightBendEquiv (P : Pivotal C) (A Y X : C) :
    (A ⟶ Y ⊗ X) ≃ₗ[ℂ] (A ⊗ Xᘁ ⟶ Y) :=
  (homCongr (Iso.refl A) (whiskerLeftIso Y (P.j X))).trans
    (rightDuality A Xᘁ Y).symm

/-- Trace-duality commutes with the right pivotal bend. -/
theorem traceDualBasis_rightBend (F : SphericalFusion C) (A Y X : C)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℂ (A ⟶ Y ⊗ X)) (a : ι) :
    F.traceDualBasis (b.map (rightBendEquiv F.toPivotal A Y X)) a =
      rightDuality Y X A (F.traceDualBasis b a) := by
  apply F.hom_ext_trace
  intro f
  rw [F.scalarTrace_comp_comm, F.traceDualBasis_pair]
  have h := scalarTrace_rightBend F ((rightBendEquiv F.toPivotal A Y X).symm f)
    (rightDuality Y X A (F.traceDualBasis b a))
  simp only [LinearEquiv.symm_apply_apply, F.traceDualBasis_pair] at h
  have he : (rightDuality A Xᘁ Y).symm
      ((rightBendEquiv F.toPivotal A Y X).symm f ≫ Y ◁ (F.j X).hom) = f := by
    simp [rightBendEquiv, homCongr]
  rw [he] at h
  simpa [Module.Basis.map_repr] using h

/-- Open right sewing of the two composition-dual maps. -/
theorem sum_rightBend_compositionDual (F : SphericalFusion C) (X : C)
    (j a : F.Label) :
    (∑ c, rightBendEquiv F.toPivotal (F.simple j) (F.simple a) X
        (F.simpleHomBasis (F.simple a ⊗ X) j c) ≫
      rightDuality (F.simple a) X (F.simple j)
        (F.compositionDual (F.simpleHomBasis (F.simple a ⊗ X) j) c)) =
      (F.dimension (F.simple j) / F.dimension (F.simple a)) •
        F.simpleProjector a (F.simple j ⊗ Xᘁ) := by
  let b := F.simpleHomBasis (F.simple a ⊗ X) j
  have hb (c) : rightDuality (F.simple a) X (F.simple j) (F.compositionDual b c) =
      F.dimension (F.simple j) •
        F.traceDualBasis (b.map (rightBendEquiv F.toPivotal (F.simple j) (F.simple a) X)) c := by
    rw [traceDualBasis_rightBend]
    simp [SphericalFusion.compositionDual]
  change (∑ c, _ ≫ rightDuality _ _ _ (F.compositionDual b c)) = _
  simp only [hb, Linear.comp_smul, ← Finset.smul_sum]
  have h := sum_basis_comp_traceDual F (F.simple j ⊗ Xᘁ) a
    (b.map (rightBendEquiv F.toPivotal (F.simple j) (F.simple a) X))
  simp only [Module.Basis.map_apply] at h
  rw [h, smul_smul, div_eq_mul_inv]

/-- Pull a bent map through the right pivotal cup. -/
theorem rightBend_factor (P : Pivotal C) {A Y X : C} (p : A ⟶ Y ⊗ X) :
    p = (rightBendEquiv P A (A ⊗ Xᘁ) X).symm (𝟙 _) ≫
      rightBendEquiv P A Y X p ▷ X := by
  conv_lhs => rw [← (rightBendEquiv P A Y X).symm_apply_apply p]
  dsimp [rightBendEquiv, homCongr, rightDuality, tensorRightHomEquiv]
  simp only [Category.assoc, id_whiskerRight, Category.comp_id, Category.id_comp]
  rw [whisker_exchange]

/-- Pull the adjoint bent map through the right evaluation cap. -/
theorem rightDuality_factor (A Y X : C) (q : Y ⊗ X ⟶ A) :
    q = rightDuality Y X A q ▷ X ≫
      (rightDuality (A ⊗ Xᘁ) X A).symm (𝟙 _) := by
  conv_lhs => rw [← (rightDuality Y X A).symm_apply_apply q]
  dsimp [rightDuality, tensorRightHomEquiv]
  simp

/-- Naturality of the inverse mixed half-braiding in its first factor. -/
@[reassoc] theorem mixedHalfBraiding_inv_first_naturality (Y U : C) {X Z : C}
    (f : X ⟶ Z) :
    U ◁ (f ▷ Y) ≫ ((mixedCenter Z Y).2.β U).inv =
      ((mixedCenter X Y).2.β U).inv ≫ (f ▷ Y) ▷ U := by
  let g : Center.ofBraidedObj X ⟶ Center.ofBraidedObj Z :=
    ⟨f, fun W => BraidedCategory.braiding_naturality_left f W⟩
  have h := (g ▷ oppositeBraidedCenter Y).comm U
  change (f ▷ Y) ▷ U ≫ ((mixedCenter Z Y).2.β U).hom =
    ((mixedCenter X Y).2.β U).hom ≫ U ◁ (f ▷ Y) at h
  apply (cancel_epi ((mixedCenter X Y).2.β U).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg (fun k => k ≫ ((mixedCenter Z Y).2.β U).inv) h.symm

/-- Attach the negative factor to an endomorphism of the right bent strand. -/
def inverseSewingMap (F : SphericalFusion C) (Y : C) (i j : F.Label) :
    (F.simple j ⊗ Yᘁ ⟶ F.simple j ⊗ Yᘁ) →ₗ[ℂ]
      (F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) where
  toFun h := F.simple i ◁
      (rightBendEquiv F.toPivotal (F.simple j) (F.simple j ⊗ Yᘁ) Y).symm (𝟙 _) ≫
    ((mixedCenter (F.simple j ⊗ Yᘁ) Y).2.β (F.simple i)).inv ≫
    (h ▷ Y ≫ (rightDuality (F.simple j ⊗ Yᘁ) Y (F.simple j)).symm (𝟙 _)) ▷ F.simple i
  map_add' f g := by
    simp [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      Preadditive.comp_add]
  map_smul' z f := by simp

/-- Factor an actual inverse crossing summand through its bent matrix unit. -/
theorem inverseCrossing_summand_sew (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) (p : F.simple j ⟶ X ⊗ Y) (q : X ⊗ Y ⟶ F.simple j) :
    F.simple i ◁ p ≫ ((mixedCenter X Y).2.β (F.simple i)).inv ≫ q ▷ F.simple i =
      inverseSewingMap F Y i j
        (rightBendEquiv F.toPivotal (F.simple j) X Y p ≫
          rightDuality X Y (F.simple j) q) := by
  conv_lhs => rw [rightBend_factor F.toPivotal p, rightDuality_factor (F.simple j) X Y q]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [mixedHalfBraiding_inv_first_naturality_assoc]
  simp [inverseSewingMap, comp_whiskerRight, Category.assoc]

/-- The inverse crossing is the right-sewn isotypic projector. -/
theorem inverseChannelCrossing_eq_sewnProjector (F : SphericalFusion C)
    (Y : C) (a i j : F.Label) :
    inverseChannelCrossing F (mixedCenter (F.simple a) Y) i j =
      (F.dimension (F.simple a))⁻¹ •
        inverseSewingMap F Y i j (F.simpleProjector a (F.simple j ⊗ Yᘁ)) := by
  change (F.dimension (F.simple j))⁻¹ •
    (∑ c, F.simple i ◁ F.simpleHomBasis (F.simple a ⊗ Y) j c ≫
      ((mixedCenter (F.simple a) Y).2.β (F.simple i)).inv ≫
      F.compositionDual (F.simpleHomBasis (F.simple a ⊗ Y) j) c ▷ F.simple i) = _
  simp_rw [inverseCrossing_summand_sew F (F.simple a) Y i j]
  rw [← map_sum, sum_rightBend_compositionDual, map_smul, smul_smul]
  congr 1
  field_simp [F.dimension_simple_ne_zero]

end VOA.Huang.NSCongruence
