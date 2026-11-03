import VOA.Huang.NSSMoveC2Inverse

/-! # Forward sewing of a central interaction as a right partial trace

The forward sewing of the `Y`-loop with a coupon `g` on `Y ⊗ Xᘁ` is rewritten,
after sliding `g` around the nested cup (`nestedCup_slide`), as a right partial
trace over `X` of the conjugated `sewnIntegrand`. Centrality of `g` is used
only in the slide.
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

/-- The left interaction loop with the coupon moved to the bottom of the
traced diagram; the remaining crossings form a loop of `Y` around `I` with
the `Xᘁ` strand moved aside. -/
theorem leftInteractionLoop_eq_coupon_first (P : Pivotal C) (Y A I : C)
    (g : Y ⊗ A ⟶ Y ⊗ A) :
    leftInteractionLoop P Y A I g = P.partialTraceLeft Y
      ((α_ Y A I).inv ≫ g ▷ I ≫ (α_ Y A I).hom ≫ Y ◁ (β_ A I).hom ≫
        (α_ Y I A).inv ≫ monodromy Y I ▷ A ≫ (α_ Y I A).hom ≫ Y ◁ (β_ A I).inv) := by
  change (β_ A I).hom ≫ P.partialTraceLeft Y _ ≫ (β_ A I).inv = _
  rw [← P.partialTraceLeft_postcomp, ← P.partialTraceLeft_precomp]
  congr 1
  have hb := braiding_tensor_left_hom Y A I
  have hn := braiding_naturality_left g I
  calc
    _ = (α_ Y A I).inv ≫ (β_ (Y ⊗ A) I).hom ≫ I ◁ g ≫ (α_ I Y A).inv ≫
          (β_ I Y).hom ▷ A ≫ (α_ Y I A).hom ≫ Y ◁ (β_ A I).inv := by
      rw [hb]; simp
    _ = (α_ Y A I).inv ≫ g ▷ I ≫ (β_ (Y ⊗ A) I).hom ≫ (α_ I Y A).inv ≫
          (β_ I Y).hom ▷ A ≫ (α_ Y I A).hom ≫ Y ◁ (β_ A I).inv := by
      rw [reassoc_of% hn]
    _ = _ := by
      rw [hb]; simp [monodromy]

/-- Sliding the right leg of a coevaluation over a strand. -/
theorem coevaluation_braiding_slide (A U : C) :
    (λ_ U).inv ≫ η_ A Aᘁ ▷ U ≫ (α_ A Aᘁ U).hom ≫ A ◁ (β_ Aᘁ U).hom =
      (ρ_ U).inv ≫ U ◁ η_ A Aᘁ ≫ (α_ U A Aᘁ).inv ≫ (β_ A U).inv ▷ Aᘁ ≫
        (α_ A U Aᘁ).hom := by
  have h := inverseBraiding_cup_slide A Aᘁ U (η_ A Aᘁ)
  calc
    _ = ((λ_ U).inv ≫ η_ A Aᘁ ▷ U ≫ (α_ A Aᘁ U).hom ≫ A ◁ (β_ Aᘁ U).hom ≫
        (α_ A U Aᘁ).inv) ≫ (α_ A U Aᘁ).hom := by simp
    _ = _ := by rw [← h]; simp

/-- Sliding a cap over a strand. -/
theorem cap_braiding_slide {A B : C} (d : A ⊗ B ⟶ 𝟙_ C) (U : C) :
    (α_ A U B).hom ≫ A ◁ (β_ B U).inv ≫ (α_ A B U).inv ≫ d ▷ U ≫ (λ_ U).hom =
      (β_ A U).hom ▷ B ≫ (α_ U A B).hom ≫ U ◁ d ≫ (ρ_ U).hom := by
  have h := braiding_naturality_left d U
  rw [braiding_tensorUnit_left, braiding_tensor_left_hom] at h
  have h2 : d ▷ U ≫ (λ_ U).hom = ((α_ A B U).hom ≫ A ◁ (β_ B U).hom ≫ (α_ A U B).inv ≫
      (β_ A U).hom ▷ B ≫ (α_ U A B).hom) ≫ U ◁ d ≫ (ρ_ U).hom := by
    rw [← cancel_mono (ρ_ U).inv]
    simpa using h
  rw [h2]
  simp

/-- The open diagram whose right partial trace is the forward sewing. -/
def forwardIntegrand (P : Pivotal C) (X Y J I : C) (m : X ⊗ Yᘁ ⟶ X ⊗ Yᘁ) :
    (J ⊗ I) ⊗ X ⟶ (J ⊗ I) ⊗ X :=
  (α_ J I X).hom ≫ J ◁ (β_ X I).inv ≫ (α_ J X I).inv ≫
    (𝟙 _ ⊗≫ J ◁ X ◁ P.cup Y ▷ I ⊗≫ J ◁ m ▷ Y ▷ I ⊗≫
      (J ⊗ X ⊗ Yᘁ) ◁ monodromy Y I ⊗≫ J ◁ X ◁ ε_ Y Yᘁ ▷ I ⊗≫ 𝟙 _) ≫
    monodromy J X ▷ I ≫ (α_ J X I).hom ≫ J ◁ (β_ X I).hom ≫ (α_ J I X).inv

/-- Conjugating by the braiding with `J ⊗ I` gives the inverse-side diagram. -/
theorem braiding_conj_forwardIntegrand (P : Pivotal C) (X Y J I : C)
    (m : X ⊗ Yᘁ ⟶ X ⊗ Yᘁ) :
    (β_ X (J ⊗ I)).hom ≫ forwardIntegrand P X Y J I m ≫ (β_ X (J ⊗ I)).inv =
      sewnIntegrand P X Y J I m := by
  rw [braiding_tensor_right_hom, braiding_tensor_right_inv]
  simp only [forwardIntegrand, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc, Iso.hom_inv_id_assoc, monodromy, comp_whiskerRight,
    hom_inv_whiskerRight_assoc]
  dsimp only [sewnIntegrand]
  rw [MonoidalCategory.tensorHom_def (β_ X J).hom, MonoidalCategory.tensorHom_def (J ◁ m),
    MonoidalCategory.tensorHom_def' (β_ J X).hom]
  dsimp only [monodromy]
  monoidal

theorem forwardSewing_leftInteractionLoop (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) (g : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ)
    (hg : ∀ e : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ, e ≫ g = g ≫ e) :
    forwardSewingMap F X i j (leftInteractionLoop F.toPivotal Y Xᘁ (F.simple i) g) =
      (β_ (F.simple j) (F.simple i)).inv ≫
        partialTraceRight F.toPivotal X
          (forwardIntegrand F.toPivotal X Y (F.simple j) (F.simple i)
            (interactionMate F.toPivotal X Y g)) := by
  rw [forwardSewingMap_monodromy]
  set J := F.simple j
  set I := F.simple i
  set P := F.toPivotal
  set h := leftInteractionLoop P Y Xᘁ I g with hh
  set m := interactionMate P X Y g with hm
  let Φ : J ⊗ X ⟶ (J ⊗ X) ⊗ (Yᘁ ⊗ Y) :=
    𝟙 _ ⊗≫ J ◁ X ◁ P.cup Y ⊗≫ J ◁ m ▷ Y ⊗≫ 𝟙 _
  let Ψ : (J ⊗ X) ⊗ (Yᘁ ⊗ Y) ⟶ J ⊗ X :=
    𝟙 _ ⊗≫ J ◁ X ◁ ε_ Y Yᘁ ⊗≫ monodromy J X ⊗≫ 𝟙 _
  calc
    _ = (β_ J I).inv ≫ (𝟙 (J ⊗ I) ⊗≫ J ◁ η_ X Xᘁ ▷ I ⊗≫
          (monodromy J X ▷ (Xᘁ ⊗ I) ≫ (J ⊗ X) ◁ h) ⊗≫
          J ◁ pivotalCap P X ▷ I ⊗≫ 𝟙 (J ⊗ I)) := by monoidal
    _ = (β_ J I).inv ≫ (𝟙 (J ⊗ I) ⊗≫ J ◁ η_ X Xᘁ ▷ I ⊗≫
          ((J ⊗ X) ◁ h ≫ monodromy J X ▷ (Xᘁ ⊗ I)) ⊗≫
          J ◁ pivotalCap P X ▷ I ⊗≫ 𝟙 (J ⊗ I)) := by rw [← whisker_exchange]
    _ = (β_ J I).inv ≫ (𝟙 (J ⊗ I) ⊗≫ J ◁ (nestedCup P X Y ≫ (X ⊗ Yᘁ) ◁ g) ▷ I ⊗≫
          J ◁ X ◁ (Yᘁ : C) ◁ ((α_ Y Xᘁ I).hom ≫ Y ◁ (β_ Xᘁ I).hom ≫ (α_ Y I Xᘁ).inv ≫
            monodromy Y I ▷ Xᘁ ≫ (α_ Y I Xᘁ).hom ≫ Y ◁ (β_ Xᘁ I).inv) ⊗≫
          J ◁ X ◁ ε_ Y Yᘁ ▷ (Xᘁ ⊗ I) ⊗≫ monodromy J X ▷ (Xᘁ ⊗ I) ⊗≫
          J ◁ pivotalCap P X ▷ I ⊗≫ 𝟙 (J ⊗ I)) := by
      rw [hh, leftInteractionLoop_eq_coupon_first]
      dsimp only [Pivotal.partialTraceLeft, nestedCup]
      monoidal
    _ = (β_ J I).inv ≫ (𝟙 (J ⊗ I) ⊗≫ J ◁ η_ X Xᘁ ▷ I ⊗≫
          (Φ ▷ (Xᘁ ⊗ I) ≫ ((J ⊗ X) ⊗ (Yᘁ ⊗ Y)) ◁ (β_ Xᘁ I).hom) ⊗≫
          (J ⊗ X ⊗ Yᘁ) ◁ (monodromy Y I ▷ Xᘁ) ⊗≫
          (((J ⊗ X) ⊗ (Yᘁ ⊗ Y)) ◁ (β_ Xᘁ I).inv ≫ Ψ ▷ (Xᘁ ⊗ I)) ⊗≫
          J ◁ pivotalCap P X ▷ I ⊗≫ 𝟙 (J ⊗ I)) := by
      rw [nestedCup_slide P X Y g hg]
      dsimp only [nestedCup, Φ, Ψ]
      monoidal
    _ = (β_ J I).inv ≫ (𝟙 (J ⊗ I) ⊗≫ J ◁ ((λ_ I).inv ≫ η_ X Xᘁ ▷ I ≫ (α_ X Xᘁ I).hom ≫
            X ◁ (β_ Xᘁ I).hom) ⊗≫ Φ ▷ (I ⊗ Xᘁ) ⊗≫
          (J ⊗ X ⊗ Yᘁ) ◁ (monodromy Y I ▷ Xᘁ) ⊗≫ Ψ ▷ (I ⊗ Xᘁ) ⊗≫
          J ◁ ((α_ X I Xᘁ).hom ≫ X ◁ (β_ Xᘁ I).inv ≫ (α_ X Xᘁ I).inv ≫
            pivotalCap P X ▷ I ≫ (λ_ I).hom) ⊗≫ 𝟙 (J ⊗ I)) := by
      rw [← whisker_exchange Φ (β_ Xᘁ I).hom, whisker_exchange Ψ (β_ Xᘁ I).inv]
      monoidal
    _ = _ := by
      rw [coevaluation_braiding_slide, cap_braiding_slide]
      dsimp only [partialTraceRight, forwardIntegrand, Φ, Ψ]
      monoidal

end VOA.Huang.NSCongruence
