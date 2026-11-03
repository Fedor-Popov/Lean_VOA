import VOA.Classification.COne.OrbPos10Monodromy
import Mathlib.CategoryTheory.Idempotents.Basic

/-! # The simple-action step for sector projections

No rigidity or simplicity of the underlying object is used. The construction
and identities of McRae's sector projections remain an explicit obligation.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open VOA VOA.Huang.HKLRational VOA.Huang.FusionUnit VOA.Huang.TensorCat
open OrbPos9 OrbPos10

section Abstract
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasZeroMorphisms C] [IsIdempotentComplete C] {A : C} [MonObj A]

/-- An action-linear idempotent of a simple action is zero or the identity.
The splitting in the underlying category is given an action before simplicity
is used; an arbitrary underlying subobject would not suffice. -/
theorem simpleAction_idempotent (Q : SimpleAction A) (p : Q.obj ⟶ Q.obj)
    (hp : p ≫ p = p) (hlinear : IsLinear Q.act Q.act p) :
    p = 0 ∨ p = 𝟙 Q.obj := by
  obtain ⟨Y, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split Q.obj p hp
  let aY : A ⊗ Y ⟶ Y := (A ◁ i) ≫ Q.act ≫ e
  have hip : i ≫ p = i := by rw [← hei, ← Category.assoc, hie, Category.id_comp]
  have hpe : p ≫ e = e := by rw [← hei, Category.assoc, hie, Category.comp_id]
  have hi : IsLinear aY Q.act i := by
    dsimp [IsLinear, aY]
    rw [Category.assoc, Category.assoc, hei, ← hlinear,
      ← Category.assoc, ← whiskerLeft_comp, hip]
  have he : IsLinear Q.act aY e := by
    dsimp [IsLinear, aY]
    rw [← Category.assoc, ← whiskerLeft_comp, hei, ← Category.assoc, hlinear,
      Category.assoc, hpe]
  have hY : IsLeftAct aY := quotient_action_laws Q.act Q.laws e i hie aY he
  letI : Mono i := ⟨fun f g h => by
    have hh := congrArg (fun t => t ≫ e) h
    simpa only [Category.assoc, hie, Category.comp_id] using hh⟩
  rcases Q.simple Y aY hY i hi inferInstance with hi0 | hiso
  · left
    rw [← hei, hi0, comp_zero]
  · right
    letI := hiso
    apply (cancel_epi i).mp
    simpa only [Category.comp_id] using hip

end Abstract

/-- OPEN: a finite resolution of the identity by action-linear idempotents
whose images satisfy the indicated monodromy equation. Orthogonality is not
required by the simple-action reduction. These are precisely the parts of
McRae's sector-projection construction consumed below. -/
def ExceptionalSectorProjections : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ Q : SimpleAction (ambient G),
        ∃ (s : Finset G) (p : G → (Q.obj ⟶ Q.obj)),
          (∑ g ∈ s, p g) = 𝟙 Q.obj ∧
          ∀ g ∈ s, p g ≫ p g = p g ∧ IsLinear Q.act Q.act (p g) ∧
            let F := fusionChoice_pbw hSR
            (BraidRibbon.braiding F (ambient G) Q.obj).hom ≫
              (BraidRibbon.braiding F Q.obj (ambient G)).hom ≫
              tensorHom F (ambientSymmetry G g).hom (𝟙 Q.obj) ≫ Q.act ≫ p g =
                Q.act ≫ p g

/-- A nonzero simple action is supported on a sector as soon as the genuine
projection identities are available. No Schur argument is applied to A ⊗ X → X. -/
theorem exceptionalSimpleActionMonodromy_of_projections
    (h : ExceptionalSectorProjections) : ExceptionalSimpleActionMonodromy := by
  classical
  intro G hG hSR E Q
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  obtain ⟨s, p, hsum, hp⟩ := h G hG hSR E Q
  have hex : ∃ g ∈ s, p g ≠ 0 := by
    by_contra hn
    push Not at hn
    exact Q.nonzero (hsum.symm.trans (Finset.sum_eq_zero hn))
  obtain ⟨g, hg, hne⟩ := hex
  obtain ⟨hid, hlin, hmono⟩ := hp g hg
  have he := (simpleAction_idempotent Q (p g) hid hlin).resolve_left hne
  refine ⟨g, ?_⟩
  simpa only [he, Category.comp_id] using hmono

end VOA.Classification.COne.OrbPos11
