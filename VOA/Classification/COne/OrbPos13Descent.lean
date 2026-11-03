import VOA.Classification.COne.OrbPos13Schur
import VOA.Classification.COne.OrbPos11Projections
import VOA.Huang.BraidRibbonHexagon

/-! Naturality of double braiding and the unit obstruction to descending it
along an action. Existence of a group label is not established here. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos13
open CategoryTheory MonoidalCategory BraidedCategory
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.HKLRational
open OrbPos9 OrbPos10 OrbPos11

section Abstract
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The genuine naturality equation. When f is an action its source is itself
a tensor product; this does not assert A-linearity of double braiding. -/
theorem doubleBraiding_action_naturality {A X : C} (a : A ⊗ X ⟶ X) :
    (A ◁ a) ≫ (β_ A X).hom ≫ (β_ X A).hom =
      (β_ A (A ⊗ X)).hom ≫ (β_ (A ⊗ X) A).hom ≫ (A ◁ a) := by
  rw [braiding_naturality_right_assoc, braiding_naturality_left]

/-- Double braiding fixes the copy of X inserted using any unit map. -/
theorem unit_doubleBraiding {A X : C} (η : 𝟙_ C ⟶ A) :
    (η ▷ X) ≫ (β_ A X).hom ≫ (β_ X A).hom = η ▷ X := by
  rw [braiding_naturality_left_assoc, braiding_naturality_right]
  have hunit : (β_ (𝟙_ C) X).hom ≫ (β_ X (𝟙_ C)).hom = 𝟙 _ := by
    apply (cancel_mono (λ_ X).hom).mp
    simp only [Category.assoc, braiding_leftUnitor, braiding_rightUnitor,
      Category.id_comp]
  rw [← Category.assoc, hunit, Category.id_comp]

/-- If a unit-preserving twisted double braiding descends through a unital
action to an endomorphism, that endomorphism must be the identity. -/
theorem descendedMonodromy_eq_id {A X : C} (η : 𝟙_ C ⟶ A)
    (a : A ⊗ X ⟶ X) (ha : (η ▷ X) ≫ a = (λ_ X).hom)
    (g : A ⟶ A) (hg : η ≫ g = η) (f : X ⟶ X)
    (hf : (β_ A X).hom ≫ (β_ X A).hom ≫ (g ▷ X) ≫ a = a ≫ f) :
    f = 𝟙 X := by
  have he := congrArg (fun t => (η ▷ X) ≫ t) hf
  have hM := unit_doubleBraiding (X := X) η
  have hunit : (η ▷ X) ≫ (β_ A X).hom ≫ (β_ X A).hom ≫ (g ▷ X) ≫ a =
      (λ_ X).hom := by
    calc
      _ = ((η ▷ X) ≫ (β_ A X).hom ≫ (β_ X A).hom) ≫ (g ▷ X) ≫ a := by
        simp only [Category.assoc]
      _ = (η ▷ X) ≫ (g ▷ X) ≫ a := by rw [hM]
      _ = (λ_ X).hom := by rw [← Category.assoc, ← comp_whiskerRight, hg, ha]
  have he' : (λ_ X).hom ≫ f = (λ_ X).hom ≫ 𝟙 X := by
    simpa only [← Category.assoc, ha, Category.comp_id] using he.symm.trans hunit
  exact (cancel_epi (λ_ X).hom).mp he'

end Abstract

/-- For the pinned extension action, even an arbitrary U-linear factorization
of the g-twisted monodromy through the action is equivalent to g-twistedness.
No simplicity, Schur lemma, or finite-order assumption is needed. -/
theorem actionMonodromyThrough_iff_factors
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)
    (ha : ActionLaws G hSR E X a) (g : G) :
    ActionMonodromyThrough G hSR X a g ↔
      ∃ f : X ⟶ X,
        (BraidRibbon.braiding (fusionChoice_pbw hSR) (ambient G) X).hom ≫
          (BraidRibbon.braiding (fusionChoice_pbw hSR) X (ambient G)).hom ≫
          tensorHom (fusionChoice_pbw hSR) (ambientSymmetry G g).hom (𝟙 X) ≫ a = a ≫ f := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := HexagonClose.braidedCategory_stronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  constructor
  · intro h
    exact ⟨𝟙 X, by simpa only [Category.comp_id] using h⟩
  · rintro ⟨f, hf⟩
    have hunit : (unitInclusion G ▷ X) ≫ a = (λ_ X).hom := by
      simpa only [E.one_eq] using ha.one_act
    have hid := descendedMonodromy_eq_id (unitInclusion G) a hunit
      (ambientSymmetry G g).hom (ambientSymmetry_unit G g) f hf
    simpa only [hid, Category.comp_id] using hf

/-- On simple actions, the existing sector-projection target is equivalent
to existence of a group monodromy label: the converse uses a singleton family.
Neither side of this equivalence is asserted unconditionally. -/
theorem exceptionalSectorProjections_iff_monodromy :
    ExceptionalSectorProjections ↔ ExceptionalSimpleActionMonodromy := by
  classical
  refine ⟨exceptionalSimpleActionMonodromy_of_projections, ?_⟩
  intro h G hG hSR E Q
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  obtain ⟨g, hg⟩ := h G hG hSR E Q
  refine ⟨{g}, fun _ => 𝟙 Q.obj, by simp, ?_⟩
  intro k hk
  have hk : k = g := Finset.mem_singleton.mp hk
  subst k
  exact ⟨by simp, isLinear_id Q.act, by simpa only [Category.comp_id] using hg⟩

end VOA.Classification.COne.OrbPos13
