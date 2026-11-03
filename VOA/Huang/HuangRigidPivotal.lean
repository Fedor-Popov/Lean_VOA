import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import VOA.Huang.TensorCategories

/-!
# The twist pivotal structure (braided rigid category with a natural twist)

For a braided right rigid category with a natural automorphism `θ` of the identity, the
**twisted Drinfeld isomorphism** `piv_X : X ≅ Xᘁᘁ` is the comparison of two right duals of `Xᘁ`:
the given `Xᘁᘁ` and `X` itself with the twisted swapped pairing
`ε' = (θ_X ▷ Xᘁ) ≫ β_{X,Xᘁ} ≫ ε_X` (`twistSwapPairing`, built from Mathlib's `exactPairing_swap`).
It is therefore an isomorphism for free (`rightDualIso`).

* `transpose_injective` — morphisms into a right dual are determined by their transposes;
* `twistPiv_evaluation` — `(piv_X ▷ Xᘁ) ≫ ε_{Xᘁ} = (θ_X ▷ Xᘁ) ≫ β ≫ ε_X`;
* `twistPiv_naturality` — naturality (needs only naturality of `θ` and of the braiding);
* `twistPivotal θ hθ : PivotalStructure 𝒞`, and `twistPivotal_unique`: any family of maps
  satisfying the evaluation identity equals `piv`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangRigid

open CategoryTheory CategoryTheory.MonoidalCategory VOA.Huang.TensorCat

universe v u

section Transpose

variable {𝒞 : Type u} [Category.{v} 𝒞] [MonoidalCategory 𝒞]

/-- Morphisms into the right dual `B` of `A` are determined by their transposes. -/
theorem transpose_injective {A B X : 𝒞} [ExactPairing A B] {g h : X ⟶ B}
    (w : (g ▷ A) ≫ ε_ A B = (h ▷ A) ≫ ε_ A B) : g = h := by
  have key : ∀ k : X ⟶ B, k = (ρ_ X).inv ≫ X ◁ η_ A B ≫ (α_ X A B).inv ≫
      ((k ▷ A) ≫ ε_ A B) ▷ B ≫ (λ_ B).hom := by
    intro k
    calc k = k ⊗≫ (B ◁ η_ A B ⊗≫ ε_ A B ▷ B) ⊗≫ 𝟙 _ := by
          rw [ExactPairing.coevaluation_evaluation'']; monoidal
      _ = 𝟙 _ ⊗≫ (k ▷ 𝟙_ 𝒞 ≫ B ◁ η_ A B) ⊗≫ ε_ A B ▷ B ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ (X ◁ η_ A B ≫ k ▷ (A ⊗ B)) ⊗≫ ε_ A B ▷ B ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
      _ = _ := by monoidal
  rw [key g, key h, w]

end Transpose

section Pivotal

variable {𝒞 : Type u} [Category.{v} 𝒞] [MonoidalCategory 𝒞] [BraidedCategory 𝒞]
  [RightRigidCategory 𝒞] (θ : ∀ X : 𝒞, X ≅ X)

/-- `X` is a right dual of `Xᘁ` via the twisted swapped pairing. -/
@[implicit_reducible]
def twistSwapPairing (X : 𝒞) : ExactPairing (Xᘁ) X :=
  letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  exactPairingCongrRight (θ X)

theorem twistSwapPairing_evaluation (X : 𝒞) :
    @ExactPairing.evaluation 𝒞 _ _ (Xᘁ) X (twistSwapPairing θ X) =
      ((θ X).hom ▷ Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := rfl

/-- The twisted Drinfeld isomorphism `X ≅ Xᘁᘁ`. -/
def twistPivIso (X : 𝒞) : X ≅ (Xᘁ)ᘁ :=
  rightDualIso (twistSwapPairing θ X) (HasRightDual.exact (X := Xᘁ))

/-- **The evaluation identity** (`PivotalTwistInput` shape). -/
theorem twistPiv_evaluation (X : 𝒞) :
    ((twistPivIso θ X).hom ▷ Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      ((θ X).hom ▷ Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
  letI := twistSwapPairing θ X
  have h := @rightAdjointMate_comp_evaluation 𝒞 _ _ (Xᘁ) (Xᘁ) ⟨(Xᘁ)ᘁ⟩ ⟨X⟩ (𝟙 _)
  rw [whiskerLeft_id, Category.id_comp] at h
  exact h

variable {θ}

/-- **Naturality of the twisted Drinfeld isomorphism.** -/
theorem twistPiv_naturality (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
    {X Y : 𝒞} (f : X ⟶ Y) :
    f ≫ (twistPivIso θ Y).hom = (twistPivIso θ X).hom ≫ (fᘁ)ᘁ := by
  apply transpose_injective (A := Yᘁ)
  rw [comp_whiskerRight_assoc, twistPiv_evaluation, comp_whiskerRight_assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, twistPiv_evaluation]
  -- `(f ▷ Yᘁ) ≫ (θ_Y ▷ Yᘁ) ≫ β ≫ ε_Y = (X ◁ fᘁ) ≫ (θ_X ▷ Xᘁ) ≫ β ≫ ε_X`
  rw [← comp_whiskerRight_assoc, hθ f, comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left_assoc, ← rightAdjointMate_comp_evaluation,
    whisker_exchange_assoc, BraidedCategory.braiding_naturality_right_assoc]

variable [Preadditive 𝒞] [Linear ℂ 𝒞]

/-- **The twist pivotal structure.** -/
def twistPivotal (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f) :
    PivotalStructure 𝒞 where
  piv := twistPivIso θ
  naturality := twistPiv_naturality hθ

/-- Uniqueness: any pivotal structure satisfying the evaluation identity is `twistPivotal`. -/
theorem twistPivotal_unique (hθ : ∀ {X Y : 𝒞} (f : X ⟶ Y), f ≫ (θ Y).hom = (θ X).hom ≫ f)
    (P : PivotalStructure 𝒞)
    (hP : ∀ X : 𝒞, ((P.piv X).hom ▷ Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      ((θ X).hom ▷ Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)) :
    P = twistPivotal hθ := by
  have hpiv : P.piv = twistPivIso θ := by
    funext X
    apply Iso.ext
    apply transpose_injective (A := Xᘁ)
    rw [hP X, twistPiv_evaluation]
  cases P
  simp only [twistPivotal] at hpiv ⊢
  subst hpiv
  rfl

end Pivotal

end VOA.Huang.HuangRigid
