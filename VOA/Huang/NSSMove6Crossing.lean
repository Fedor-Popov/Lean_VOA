import VOA.Huang.NSSMove6Sewing

/-! # Sewing the second label of the actual forward mixed crossing -/
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

/-- Express the pivotal adjoint bend through the ordinary duality equivalence. -/
theorem leftBendAdjoint_eq_duality (P : Pivotal C) {A X Y : C}
    (g : X ⊗ Y ⟶ A) :
    leftBendAdjoint P g =
      leftDuality Y Xᘁ A ((P.j X).inv ▷ Y ≫ g) := by
  dsimp [leftBendAdjoint, leftDuality, tensorLeftHomEquiv, Pivotal.cup]
  monoidal

/-- The cap inverse to the pivotal adjoint bend. -/
def leftUnbendAdjoint (P : Pivotal C) {A X Y : C} (f : Y ⟶ Xᘁ ⊗ A) :
    X ⊗ Y ⟶ A :=
  (P.j X).hom ▷ Y ≫ (leftDuality Y Xᘁ A).symm f

/-- Unbending the adjoint returns the original morphism. -/
theorem leftUnbendAdjoint_leftBend (P : Pivotal C) {A X Y : C}
    (g : X ⊗ Y ⟶ A) : leftUnbendAdjoint P (leftBendAdjoint P g) = g := by
  rw [leftBendAdjoint_eq_duality]
  simp [leftUnbendAdjoint]

/-- Pull a map on the unbent strand through the cup. -/
theorem leftDuality_factor (A X Y : C) (f : A ⟶ X ⊗ Y) :
    f = leftDuality A X (Xᘁ ⊗ A) (𝟙 _) ≫
      X ◁ (leftDuality A X Y).symm f := by
  conv_lhs => rw [← (leftDuality A X Y).apply_symm_apply f]
  dsimp [leftDuality, tensorLeftHomEquiv]
  simp

/-- Pull a map on the bent strand through the pivotal cap. -/
theorem leftBendAdjoint_factor (P : Pivotal C) {A X Y : C}
    (g : X ⊗ Y ⟶ A) :
    g = X ◁ leftBendAdjoint P g ≫ leftUnbendAdjoint P (𝟙 (Xᘁ ⊗ A)) := by
  conv_lhs => rw [← leftUnbendAdjoint_leftBend P g]
  dsimp [leftUnbendAdjoint, leftDuality, tensorLeftHomEquiv]
  rw [whisker_exchange_assoc]
  monoidal

/-- Naturality of the mixed half-braiding in the negative braided factor. -/
@[reassoc] theorem mixedHalfBraiding_second_naturality (X U : C) {Y Z : C} (f : Y ⟶ Z) :
    (X ◁ f) ▷ U ≫ ((mixedCenter X Z).2.β U).hom =
      ((mixedCenter X Y).2.β U).hom ≫ U ◁ (X ◁ f) := by
  let g : oppositeBraidedCenter Y ⟶ oppositeBraidedCenter Z :=
    ⟨f, fun W => BraidedCategory.braiding_inv_naturality_left f W⟩
  exact (Center.ofBraidedObj X ◁ g).comm U

/-- Attach the positive strand and its cup and pivotal cap to an arbitrary
endomorphism on the bent strand. This map does not depend on the second label. -/
def forwardSewingMap (F : SphericalFusion C) (X : C) (i j : F.Label) :
    (Xᘁ ⊗ F.simple i ⟶ Xᘁ ⊗ F.simple i) →ₗ[ℂ]
      (F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) where
  toFun h := leftDuality (F.simple i) X (Xᘁ ⊗ F.simple i) (𝟙 _) ▷ F.simple j ≫
    ((mixedCenter X (Xᘁ ⊗ F.simple i)).2.β (F.simple j)).hom ≫
    F.simple j ◁ (X ◁ h ≫ leftUnbendAdjoint F.toPivotal (𝟙 (Xᘁ ⊗ F.simple i)))
  map_add' f g := by
    simp [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' z f := by simp

/-- The actual crossing summand factors through the open bent matrix unit. -/
theorem forwardCrossing_summand_sew (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) (p : F.simple i ⟶ X ⊗ Y) (q : X ⊗ Y ⟶ F.simple i) :
    p ▷ F.simple j ≫ ((mixedCenter X Y).2.β (F.simple j)).hom ≫ F.simple j ◁ q =
      forwardSewingMap F X i j
        ((leftDuality (F.simple i) X Y).symm p ≫ leftBendAdjoint F.toPivotal q) := by
  conv_lhs => rw [leftDuality_factor (F.simple i) X Y p,
    leftBendAdjoint_factor F.toPivotal q]
  simp only [comp_whiskerRight, Category.assoc]
  rw [mixedHalfBraiding_second_naturality_assoc]
  simp [forwardSewingMap, whiskerLeft_comp, Category.assoc]

/-- The forward crossing is the sewn simple projector, with the inverse
second-label dimension dictated by the dual-basis calculation. -/
theorem forwardChannelCrossing_eq_sewnProjector (F : SphericalFusion C)
    (X : C) (s i j : F.Label) :
    forwardChannelCrossing F (mixedCenter X (F.simple s)) i j =
      (F.dimension (F.simple s))⁻¹ •
        forwardSewingMap F X i j (F.simpleProjector s (Xᘁ ⊗ F.simple i)) := by
  change (F.dimension (F.simple i))⁻¹ •
    (∑ a, F.simpleHomBasis (X ⊗ F.simple s) i a ▷ F.simple j ≫
      ((mixedCenter X (F.simple s)).2.β (F.simple j)).hom ≫
      F.simple j ◁ F.compositionDual (F.simpleHomBasis (X ⊗ F.simple s) i) a) = _
  simp_rw [forwardCrossing_summand_sew F X (F.simple s) i j]
  rw [← map_sum]
  rw [sum_leftBend_compositionDual, map_smul, smul_smul]
  congr 1
  field_simp [F.dimension_simple_ne_zero]

/-- The second mixed-label sum of the actual forward crossing is evaluated
as an open monodromy-loop diagram, not merely after a trace. -/
theorem sum_secondLabel_forwardChannelCrossing (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (X : C) (b i j : F.Label) :
    (∑ s, categoricalS F (F.dualLabel s) b •
      forwardChannelCrossing F (mixedCenter X (F.simple s)) i j) =
      forwardSewingMap F X i j
        (monodromyLoop F.toPivotal (F.simple (F.dualLabel b))ᘁ
          (Xᘁ ⊗ F.simple i)) := by
  simp only [forwardChannelCrossing_eq_sewnProjector, smul_smul]
  simp_rw [categoricalS_dual_left F R, categoricalS_symm F R _ (F.dualLabel b)]
  rw [monodromyLoop_eq_sum_projectors]
  simp only [map_sum, map_smul, div_eq_mul_inv]

/-- The double Fourier sum is a single sum of explicit open loop diagrams. -/
theorem mixedForwardExchange_eq_singleLoopSum (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) (a b i j : F.Label) :
    (∑ q : F.Label × F.Label, mixedExchangeCoefficient F a b q •
      forwardChannelCrossing F (mixedCenter (F.simple q.1) (F.simple q.2)) i j) =
      F.globalDimension⁻¹ • ∑ r, categoricalS F r a •
        forwardSewingMap F (F.simple r) i j
          (monodromyLoop F.toPivotal (F.simple (F.dualLabel b))ᘁ
            ((F.simple r)ᘁ ⊗ F.simple i)) := by
  rw [Fintype.sum_prod_type]
  simp only [mixedExchangeCoefficient, mul_smul, ← Finset.smul_sum]
  simp_rw [sum_secondLabel_forwardChannelCrossing F R]

/-- A proved partial sewing result: all second-label sums, with arbitrary
positive object and both exterior labels. -/
def MixedForwardSecondLabelSewing (F : SphericalFusion C) : Prop :=
  ∀ (X : C) (b i j : F.Label),
    (∑ s, categoricalS F (F.dualLabel s) b •
      forwardChannelCrossing F (mixedCenter X (F.simple s)) i j) =
      forwardSewingMap F X i j
        (monodromyLoop F.toPivotal (F.simple (F.dualLabel b))ᘁ
          (Xᘁ ⊗ F.simple i))

theorem mixedForwardSecondLabelSewing_holds (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) : MixedForwardSecondLabelSewing F :=
  sum_secondLabel_forwardChannelCrossing F R

end VOA.Huang.NSCongruence
