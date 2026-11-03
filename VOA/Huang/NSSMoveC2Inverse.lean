import VOA.Huang.NSSMoveC1Slide

/-! # Inverse sewing of an interaction loop as one left partial trace

The inverse sewing of the `X`-loop with an arbitrary interaction `m` on
`X ⊗ Yᘁ` is rewritten as a single left partial trace over `X` of an explicit
open diagram `sewnIntegrand`. Only braided-monoidal moves are used.
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

/-- The common open diagram: `X` crosses `J`, the `Y`-loop is created between
`X` and `I`, the interaction `m` acts on `X ⊗ Yᘁ` while `Y` encircles `I`,
the `Y`-loop is closed and `X` crosses back, completing a loop around `J`. -/
def sewnIntegrand (P : Pivotal C) (X Y J I : C) (m : X ⊗ Yᘁ ⟶ X ⊗ Yᘁ) :
    X ⊗ (J ⊗ I) ⟶ X ⊗ (J ⊗ I) :=
  (α_ X J I).inv ≫ ((β_ X J).hom ⊗ₘ ((λ_ I).inv ≫ P.cup Y ▷ I)) ⊗≫
    ((J ◁ m) ⊗ₘ monodromy Y I) ⊗≫
    ((β_ J X).hom ⊗ₘ (ε_ Y Yᘁ ▷ I ≫ (λ_ I).hom)) ⊗≫ 𝟙 _

theorem inverseSewing_rightInteractionLoop (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) (m : X ⊗ Yᘁ ⟶ X ⊗ Yᘁ) :
    inverseSewingMap F Y i j (rightInteractionLoop F.toPivotal X (F.simple j) Yᘁ m) =
      (β_ (F.simple j) (F.simple i)).inv ≫
        F.toPivotal.partialTraceLeft X
          (sewnIntegrand F.toPivotal X Y (F.simple j) (F.simple i) m) := by
  rw [inverseSewingMap_monodromy]
  set J := F.simple j
  set I := F.simple i
  set P := F.toPivotal
  let A : J ⊗ I ⟶ ((J ⊗ Yᘁ) ⊗ Y) ⊗ I :=
    𝟙 _ ⊗≫ J ◁ (P.cup Y ▷ I) ⊗≫ J ◁ (Yᘁ ◁ monodromy Y I) ⊗≫ 𝟙 _
  let B : ((J ⊗ Yᘁ) ⊗ Y) ⊗ I ⟶ J ⊗ I := 𝟙 _ ⊗≫ (J ◁ ε_ Y Yᘁ) ▷ I ⊗≫ 𝟙 _
  let R : X ⊗ (J ⊗ Yᘁ) ⟶ X ⊗ (J ⊗ Yᘁ) :=
    (α_ X J Yᘁ).inv ≫ (β_ X J).hom ▷ Yᘁ ≫ (α_ J X Yᘁ).hom ≫
      J ◁ m ≫ (α_ J X Yᘁ).inv ≫ (β_ J X).hom ▷ Yᘁ ≫ (α_ X J Yᘁ).hom
  have hR : rightInteractionLoop P X J Yᘁ m = P.partialTraceLeft X R := rfl
  calc
    _ = (β_ J I).inv ≫ A ≫ (P.partialTraceLeft X R ▷ Y) ▷ I ≫ B := by
      rw [hR]; dsimp only [A, B]; monoidal
    _ = _ := by
      rw [← P.partialTraceLeft_whisker, ← P.partialTraceLeft_whisker,
        ← P.partialTraceLeft_postcomp, ← P.partialTraceLeft_precomp]
      congr 1
      apply congrArg (P.partialTraceLeft X)
      dsimp only [A, B, R, sewnIntegrand]
      calc
        _ = (α_ X J I).inv ≫ ((β_ X J).hom ⊗ₘ ((λ_ I).inv ≫ P.cup Y ▷ I ≫
              (α_ Yᘁ Y I).hom ≫ Yᘁ ◁ monodromy Y I)) ⊗≫ (J ◁ m) ▷ (Y ⊗ I) ⊗≫
            ((β_ J X).hom ⊗ₘ (ε_ Y Yᘁ ▷ I ≫ (λ_ I).hom)) ⊗≫ 𝟙 _ := by
          rw [MonoidalCategory.tensorHom_def', MonoidalCategory.tensorHom_def]; monoidal
        _ = _ := by
          rw [MonoidalCategory.tensorHom_def (β_ X J).hom,
            MonoidalCategory.tensorHom_def (β_ X J).hom, MonoidalCategory.tensorHom_def' (J ◁ m)]
          monoidal

end VOA.Huang.NSCongruence
