import VOA.Classification.COne.OrbPos11Fields
import VOA.Classification.COne.OrbPos11Grid

/-! # Simplicity of the action implies irreducibility of its fractional fields -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct VOA.Huang.TensorCat
open VOA.Huang.HKLRational VOA.Huang.TensorCat.RepPackaging
open CategoryTheory CategoryTheory.Limits MonoidalCategory OrbPos9 OrbPos10 OrbPos2

section Abstract
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- Action laws descend to a stable subobject; the inclusion, not an arbitrary
underlying splitting, must intertwine the actions. -/
theorem subaction_laws {X Y : C} (aX : A ⊗ X ⟶ X) (hX : IsLeftAct aX)
    (aY : A ⊗ Y ⟶ Y) (i : Y ⟶ X) [Mono i] (hi : IsLinear aY aX i) :
    IsLeftAct aY := by
  change (A ◁ i) ≫ aX = aY ≫ i at hi
  constructor
  · apply (cancel_mono i).mp
    rw [Category.assoc, ← hi, ← Category.assoc, ← whisker_exchange,
      Category.assoc, hX.one_act, MonoidalCategory.leftUnitor_naturality]
  · apply (cancel_mono i).mp
    simp only [Category.assoc]
    rw [← hi, ← whiskerLeft_comp_assoc, ← hi, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← associator_naturality_right_assoc, ← hX.mul_act,
      ← Category.assoc, ← whisker_exchange, Category.assoc]

end Abstract

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)

set_option maxHeartbeats 1000000 in
-- Fusion maps on concrete lattice carriers require additional unfolding.
/-- Stability under all coefficients of a simple action leaves only the zero
subspace and the full space. This does not assume a twisted module exists. -/
theorem simpleAction_coefficient_irreducible :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∀ (Q : SimpleAction (ambient G)) (P : Submodule ℂ Q.obj.carrier),
      (∀ z v x, x ∈ P → (actionIntertwiner G hSR Q.obj Q.act).val z v x ∈ P) →
        P = ⊥ ∨ P = ⊤ := by
  let F := fusionChoice_pbw hSR
  letI := monoidalCategoryOfStronglyRational_pbw F hSR
  letI := E.monoid
  intro Q P hP
  let S : WeakModule.Submodule' Q.obj.isMod.toWeakModule :=
    ⟨P, fun v k x hx => by
      have hh := hP (k : ℂ) v.1 x hx
      rw [actionIntertwiner_fixed G hSR E Q.obj Q.act Q.laws,
        moduleModes_apply_intCast] at hh
      exact hh⟩
  let Y := Ordinary.of (Q.obj.isMod.submodule S)
  let i : Y ⟶ Q.obj := ⟨P.subtype, fun _ _ _ => rfl⟩
  have hi : Mono i := (mono_iff_injective i).mpr Subtype.val_injective
  letI := hi
  obtain ⟨r, hir⟩ := ordinary_mono_splits hSR i hi
  have hfix (z : Q.obj.carrier) (hz : z ∈ P) : i.val (r.val z) = z := by
    have he := congrArg (fun f : Y ⟶ Y => f.val ⟨z, hz⟩) hir
    exact congrArg Subtype.val he
  let aY : ambient G ⊗ Y ⟶ Y := (ambient G ◁ i) ≫ Q.act ≫ r
  have hlinear : IsLinear aY Q.act i := by
    apply tensor_hom_ext F
    intro z v y
    change Q.act.val ((tensorHom F (𝟙 (ambient G)) i).val
      ((F (ambient G) Y).intertwiner.val z v y)) =
      i.val (r.val (Q.act.val ((tensorHom F (𝟙 (ambient G)) i).val
        ((F (ambient G) Y).intertwiner.val z v y))))
    rw [tensorHom_intertwiner, Ordinary.id_apply]
    exact (hfix _ (hP z v y.val y.property)).symm
  have hY := subaction_laws Q.act Q.laws aY i hlinear
  rcases Q.simple Y aY hY i hlinear hi with hz | hiso
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have he := congrArg (fun f : Y ⟶ Q.obj => f.val ⟨x, hx⟩) hz
    exact he
  · right
    letI := hiso
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := (epi_iff_surjective i).mp inferInstance x
    exact hy ▸ y.property

/-- Simplicity supplies nontriviality of the actual carrier. -/
theorem simpleAction_nontrivial :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∀ Q : SimpleAction (ambient G), Nontrivial Q.obj.carrier := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  intro Q
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  letI := hs
  exact Q.nonzero (Ordinary.hom_ext _ _ (fun _ => Subsingleton.elim _ _))

/-- The reconstructed module is irreducible solely from simplicity of the
action; no classification by lowest weight or extra irreducibility input. -/
theorem actionTwistedModule_irreducible :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ∀ (Q : SimpleAction (ambient G)) (g : G)
      (hm : ActionMonodromyThrough G hSR Q.obj Q.act g)
      {N : ℕ} (hN : 0 < N) (hg : g.1 ^ N = 1)
      (hJ : TwistedJacobi g.1 N (actionModes G hSR Q.obj Q.act N)),
      TwistedIrreducible (actionTwistedModule G hSR E Q.obj Q.act Q.laws g hm hN hJ) := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  intro Q g hm N hN hg hJ
  refine ⟨simpleAction_nontrivial G hSR E Q, fun P hP => ?_⟩
  apply simpleAction_coefficient_irreducible G hSR E Q P
  exact (actionModes_stable_iff G hSR Q.obj Q.act g hm hN hg P).mp hP

end VOA.Classification.COne.OrbPos11
