import VOA.Huang.NSSMove7Trace

/-! # Loop transposition when one of its colors is transparent

This is a genuine special case of `MixedLoopTranspose`, not the general
modular-category assertion. It will in particular cover tensor-unit colors.
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

/-- A loop ignores a right tensor factor that centralizes its color.
The proof expands both hexagons before taking the partial trace. -/
theorem monodromyLoop_tensor_right_of_centralizes (P : Pivotal C) (X A B : C)
    (h : monodromy X B = 𝟙 _) :
    monodromyLoop P X (A ⊗ B) = monodromyLoop P X A ▷ B := by
  have hm : monodromy X (A ⊗ B) =
      (α_ X A B).inv ≫ monodromy X A ▷ B ≫ (α_ X A B).hom := by
    dsimp only [monodromy]
    rw [braiding_tensor_right_hom, braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [monodromy] at h
    rw [← whiskerLeft_comp_assoc, h]
    simp
  rw [monodromyLoop, hm, P.partialTraceLeft_whisker]
  rfl

/-- The corresponding left spectator formula, transported through the braiding. -/
theorem monodromyLoop_tensor_left_of_centralizes (P : Pivotal C) (X A B : C)
    (h : monodromy X A = 𝟙 _) :
    monodromyLoop P X (A ⊗ B) = A ◁ monodromyLoop P X B := by
  apply (cancel_mono (β_ A B).hom).mp
  rw [← monodromyLoop_naturality, monodromyLoop_tensor_right_of_centralizes P X B A h,
    braiding_naturality_right]

/-- A transparent color contributes just its spherical dimension. -/
theorem monodromyLoop_of_centralizes (F : SphericalFusion C) (X A : C)
    (h : monodromy X A = 𝟙 _) :
    monodromyLoop F.toPivotal X A = F.dimension X • 𝟙 A := by
  rw [monodromyLoop, h, ← whiskerLeft_id X A, F.partialTraceLeft_whiskerLeft]

/-- An insertion supported on the right exterior strand can be pulled out
of inverse sewing, with no hypothesis on that endomorphism. -/
theorem inverseSewingMap_whiskerRight (F : SphericalFusion C) (Y : C)
    (i j : F.Label) (f : F.simple j ⟶ F.simple j) :
    inverseSewingMap F Y i j (f ▷ Yᘁ) =
      inverseSewingMap F Y i j (𝟙 _) ≫ f ▷ F.simple i := by
  rw [inverseSewingMap_explicit, inverseSewingMap_explicit]
  have he : (f ▷ Yᘁ) ▷ Y ≫ (α_ (F.simple j) Yᘁ Y).hom ≫
      F.simple j ◁ ε_ Y Yᘁ ≫ (ρ_ (F.simple j)).hom =
      (α_ (F.simple j) Yᘁ Y).hom ≫ F.simple j ◁ ε_ Y Yᘁ ≫
        (ρ_ (F.simple j)).hom ≫ f := by
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      rightUnitor_naturality]
  calc
    _ = 𝟙 (F.simple i ⊗ F.simple j) ⊗≫
        (F.simple i ⊗ F.simple j) ◁ F.toPivotal.cup Y ⊗≫
        (β_ (F.simple j ⊗ Yᘁ) (F.simple i)).inv ▷ Y ⊗≫
        (F.simple j ⊗ Yᘁ) ◁ (β_ (F.simple i) Y).hom ⊗≫
        ((f ▷ Yᘁ) ▷ Y ≫ (α_ (F.simple j) Yᘁ Y).hom ≫
          F.simple j ◁ ε_ Y Yᘁ ≫ (ρ_ (F.simple j)).hom) ▷ F.simple i := by monoidal
    _ = _ := by rw [he]; monoidal

/-- An insertion supported on the left exterior strand pulls out of forward sewing. -/
theorem forwardSewingMap_whiskerLeft (F : SphericalFusion C) (X : C)
    (i j : F.Label) (f : F.simple i ⟶ F.simple i) :
    forwardSewingMap F X i j (Xᘁ ◁ f) =
      forwardSewingMap F X i j (𝟙 _) ≫ F.simple j ◁ f := by
  rw [forwardSewingMap_explicit, forwardSewingMap_explicit]
  have he : X ◁ (Xᘁ ◁ f) ≫ (α_ X Xᘁ (F.simple i)).inv ≫
      pivotalCap F.toPivotal X ▷ F.simple i ≫ (λ_ (F.simple i)).hom =
      (α_ X Xᘁ (F.simple i)).inv ≫ pivotalCap F.toPivotal X ▷ F.simple i ≫
        (λ_ (F.simple i)).hom ≫ f := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      leftUnitor_naturality]
  calc
    _ = 𝟙 (F.simple i ⊗ F.simple j) ⊗≫ η_ X Xᘁ ▷ (F.simple i ⊗ F.simple j) ⊗≫
        X ◁ (β_ (F.simple j) (Xᘁ ⊗ F.simple i)).inv ⊗≫
        (β_ X (F.simple j)).hom ▷ (Xᘁ ⊗ F.simple i) ⊗≫
        F.simple j ◁ (X ◁ (Xᘁ ◁ f) ≫ (α_ X Xᘁ (F.simple i)).inv ≫
          pivotalCap F.toPivotal X ▷ F.simple i ≫ (λ_ (F.simple i)).hom) := by monoidal
    _ = _ := by rw [he]; monoidal

/-- A named special case: the color and its chosen right dual are transparent. -/
def TransparentDualPair (X : C) : Prop :=
  (∀ Z : C, monodromy X Z = 𝟙 _) ∧ (∀ Z : C, monodromy Z Xᘁ = 𝟙 _)

/-- Transposition with a transparent negative color, for arbitrary positive object. -/
theorem loopTranspose_of_transparent_negative (F : SphericalFusion C) (X Y : C)
    (hY : TransparentDualPair Y) (i j : F.Label) :
    forwardSewingMap F X i j (monodromyLoop F.toPivotal Y (Xᘁ ⊗ F.simple i)) =
      inverseSewingMap F Y i j (monodromyLoop F.toPivotal X (F.simple j ⊗ Yᘁ)) := by
  rw [monodromyLoop_of_centralizes F Y _ (hY.1 _), map_smul,
    forwardSewingMap_id, monodromyLoop_tensor_right_of_centralizes _ _ _ _ (hY.2 _),
    inverseSewingMap_whiskerRight, inverseSewingMap_id,
    monodromyLoop_of_centralizes F Y _ (hY.1 _)]
  simp

/-- Transposition with a transparent positive color, for arbitrary negative object. -/
theorem loopTranspose_of_transparent_positive (F : SphericalFusion C) (X Y : C)
    (hX : TransparentDualPair X) (i j : F.Label) :
    forwardSewingMap F X i j (monodromyLoop F.toPivotal Y (Xᘁ ⊗ F.simple i)) =
      inverseSewingMap F Y i j (monodromyLoop F.toPivotal X (F.simple j ⊗ Yᘁ)) := by
  rw [monodromyLoop_tensor_left_of_centralizes _ _ _ _ (hX.2 _),
    forwardSewingMap_whiskerLeft, forwardSewingMap_id,
    monodromyLoop_of_centralizes F X _ (hX.1 _),
    monodromyLoop_of_centralizes F X _ (hX.1 _), map_smul, inverseSewingMap_id]
  simp

/-- Centralization is symmetric in its two colors. -/
theorem monodromy_eq_id_symm (X Y : C) (h : monodromy X Y = 𝟙 _) :
    monodromy Y X = 𝟙 _ := by
  apply (cancel_epi (β_ X Y).hom).mp
  simpa only [monodromy, Category.assoc, Category.comp_id, Category.id_comp] using
    congrArg (fun f => f ≫ (β_ X Y).hom) h

/-- Transport trivial monodromy along an isomorphism of its first color. -/
theorem monodromy_eq_id_of_iso {X Y : C} (e : X ≅ Y) (Z : C)
    (h : monodromy Y Z = 𝟙 _) : monodromy X Z = 𝟙 _ := by
  have hn : e.hom ▷ Z ≫ monodromy Y Z = monodromy X Z ≫ e.hom ▷ Z := by
    simp [monodromy]
  apply (cancel_mono (e.hom ▷ Z)).mp
  rw [← hn, h]
  simp

/-- Both members of the chosen dual pair of a unit object are transparent. -/
theorem transparentDualPair_of_iso_unit (P : Pivotal C) {X : C} (e : X ≅ 𝟙_ C) :
    TransparentDualPair X := by
  let de : Xᘁ ≅ (𝟙_ C)ᘁ :=
    { hom := e.invᘁ
      inv := e.homᘁ
      hom_inv_id := by rw [← comp_rightAdjointMate]; simp
      inv_hom_id := by rw [← comp_rightAdjointMate]; simp }
  constructor
  · intro Z
    exact monodromy_eq_id_of_iso e Z (by simp [monodromy])
  · intro Z
    apply monodromy_eq_id_symm
    exact monodromy_eq_id_of_iso (de ≪≫ P.dualUnit.symm) Z (by simp [monodromy])

/-- The unit label is covered without imposing transparency on the category. -/
theorem transparentDualPair_unitLabel (F : SphericalFusion C) :
    TransparentDualPair (F.simple F.unitLabel) :=
  transparentDualPair_of_iso_unit F.toPivotal F.unitIso

/-- A named proved part of the original target, containing all exterior labels
and either tensor-unit loop color. -/
def MixedUnitLoopTranspose (F : SphericalFusion C) : Prop :=
  ∀ r b i j : F.Label, r = F.unitLabel ∨ b = F.unitLabel →
    forwardSewingMap F (F.simple r) i j
      (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) =
    inverseSewingMap F (F.simple b) i j
      (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ))

/-- Every spherical braided fusion category satisfies the unit-color portion. -/
theorem mixedUnitLoopTranspose_holds (F : SphericalFusion C) :
    MixedUnitLoopTranspose F := by
  intro r b i j h
  rcases h with h | h
  · subst r
    exact loopTranspose_of_transparent_positive F _ _ (transparentDualPair_unitLabel F) i j
  · subst b
    exact loopTranspose_of_transparent_negative F _ _ (transparentDualPair_unitLabel F) i j

end VOA.Huang.NSCongruence
