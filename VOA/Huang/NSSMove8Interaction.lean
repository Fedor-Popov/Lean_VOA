import VOA.Huang.NSSMove7Assembly

/-! # Linear insertion of the interaction between the two loop colors

These maps retain the entire open sewing diagram. The identity insertion is
proved to transpose. No transposition for arbitrary insertions is assumed.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Open loop with an arbitrary insertion replacing its right interaction. -/
def rightInteractionLoop (P : Pivotal C) (X A B : C) :
    (X ⊗ B ⟶ X ⊗ B) →ₗ[ℂ] (A ⊗ B ⟶ A ⊗ B) where
  toFun h := P.partialTraceLeft X
    ((α_ X A B).inv ≫ (β_ X A).hom ▷ B ≫ (α_ A X B).hom ≫
      A ◁ h ≫ (α_ A X B).inv ≫ (β_ A X).hom ▷ B ≫ (α_ X A B).hom)
  map_add' f g := by
    change P.partialTraceLeftLinear X _ _ _ = _
    simp [MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add,
      Preadditive.add_comp, map_add]
    rfl
  map_smul' z f := by
    change P.partialTraceLeftLinear X _ _ _ = _
    simp
    rfl

/-- Inserting the actual right monodromy recovers the original loop. -/
theorem rightInteractionLoop_monodromy (P : Pivotal C) (X A B : C) :
    rightInteractionLoop P X A B (monodromy X B) = monodromyLoop P X (A ⊗ B) := by
  dsimp only [rightInteractionLoop, LinearMap.coe_mk, AddHom.coe_mk, monodromyLoop]
  congr 1
  simp only [monodromy, braiding_tensor_right_hom, braiding_tensor_left_hom,
    Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]

/-- With the interaction removed, the loop is confined to the left spectator. -/
theorem rightInteractionLoop_id (P : Pivotal C) (X A B : C) :
    rightInteractionLoop P X A B (𝟙 _) = monodromyLoop P X A ▷ B := by
  dsimp only [rightInteractionLoop, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc]
  exact P.partialTraceLeft_whisker X (monodromy X A) B

/-- The left insertion is transported by the exterior braiding. -/
def leftInteractionLoop (P : Pivotal C) (X A B : C) :
    (X ⊗ A ⟶ X ⊗ A) →ₗ[ℂ] (A ⊗ B ⟶ A ⊗ B) where
  toFun h := (β_ A B).hom ≫ rightInteractionLoop P X B A h ≫ (β_ A B).inv
  map_add' f g := by simp [map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' z f := by simp

theorem leftInteractionLoop_monodromy (P : Pivotal C) (X A B : C) :
    leftInteractionLoop P X A B (monodromy X A) = monodromyLoop P X (A ⊗ B) := by
  change (β_ A B).hom ≫ rightInteractionLoop P X B A _ ≫ _ = _
  rw [rightInteractionLoop_monodromy, ← Category.assoc, monodromyLoop_naturality]
  simp

theorem leftInteractionLoop_id (P : Pivotal C) (X A B : C) :
    leftInteractionLoop P X A B (𝟙 _) = A ◁ monodromyLoop P X B := by
  change (β_ A B).hom ≫ rightInteractionLoop P X B A _ ≫ _ = _
  rw [rightInteractionLoop_id, ← braiding_naturality_right_assoc]
  simp

/-- Linear mate transport between the two interaction objects. -/
def interactionMate (P : Pivotal C) (X Y : C) :
    (Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ) →ₗ[ℂ] (X ⊗ Yᘁ ⟶ X ⊗ Yᘁ) where
  toFun h := (dualMonodromyPairIso P X Y).hom ≫ hᘁ ≫
    (dualMonodromyPairIso P X Y).inv
  map_add' f g := by simp [rightAdjointMate, Preadditive.add_comp, Preadditive.comp_add,
    MonoidalPreadditive.add_whiskerRight, MonoidalPreadditive.whiskerLeft_add]
  map_smul' z f := by simp [rightAdjointMate]

@[simp] theorem interactionMate_id (P : Pivotal C) (X Y : C) :
    interactionMate P X Y (𝟙 _) = 𝟙 _ := by simp [interactionMate]

theorem interactionMate_monodromy (P : Pivotal C) (X Y : C) :
    interactionMate P X Y (monodromy Y Xᘁ) = monodromy X Yᘁ := by
  change (dualMonodromyPairIso P X Y).hom ≫ _ ≫ _ = _
  rw [← Category.assoc, dualMonodromyPairIso_intertwines]
  simp

/-- Difference of the two complete sewn diagrams, linear in their interaction.
Vanishing at the actual monodromy is exactly the desired local equality. -/
def interactionTransposeDefect (F : SphericalFusion C) (X Y : C) (i j : F.Label) :
    (Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ) →ₗ[ℂ] (F.simple i ⊗ F.simple j ⟶ F.simple j ⊗ F.simple i) :=
  (forwardSewingMap F X i j).comp (leftInteractionLoop F.toPivotal Y Xᘁ (F.simple i)) -
    (inverseSewingMap F Y i j).comp
      ((rightInteractionLoop F.toPivotal X (F.simple j) Yᘁ).comp
        (interactionMate F.toPivotal X Y))

/-- Identity insertion transposes without any scalarity hypothesis on the
actual monodromy. This is an equality of open morphisms. -/
theorem interactionTransposeDefect_id (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) : interactionTransposeDefect F X Y i j (𝟙 _) = 0 := by
  simp only [interactionTransposeDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    leftInteractionLoop_id, interactionMate_id, rightInteractionLoop_id, sub_eq_zero]
  rw [forwardSewingMap_whiskerLeft, inverseSewingMap_whiskerRight,
    forwardSewingMap_id, inverseSewingMap_id]
  simp only [Category.assoc]
  rw [whisker_exchange]

/-- The linear defect evaluates to the exact original loop-transposition gap. -/
theorem interactionTransposeDefect_monodromy (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) :
    interactionTransposeDefect F X Y i j (monodromy Y Xᘁ) =
      forwardSewingMap F X i j (monodromyLoop F.toPivotal Y (Xᘁ ⊗ F.simple i)) -
      inverseSewingMap F Y i j (monodromyLoop F.toPivotal X (F.simple j ⊗ Yᘁ)) := by
  simp only [interactionTransposeDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    leftInteractionLoop_monodromy, interactionMate_monodromy, rightInteractionLoop_monodromy]

/-- For a simple interaction object, every insertion transposes. This is the
full linear-map simple case; extending it to summands requires compatibility
with their embeddings into the separated loop colors. -/
theorem interactionTransposeDefect_eq_zero_of_simple (F : SphericalFusion C)
    (X Y : C) [Simple (Y ⊗ Xᘁ)] (i j : F.Label) :
    interactionTransposeDefect F X Y i j = 0 := by
  letI := F.homFinite (Y ⊗ Xᘁ) (Y ⊗ Xᘁ)
  apply LinearMap.ext
  intro h
  change interactionTransposeDefect F X Y i j h = 0
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ h
  rw [← hz, map_smul, interactionTransposeDefect_id, smul_zero]

end VOA.Huang.NSCongruence
