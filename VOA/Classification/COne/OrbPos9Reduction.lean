import VOA.Classification.COne.OrbPos9Associativity
import VOA.Classification.COne.OrbPos9Untwisted

/-!
# The precise remaining categorical obligations for exceptional DRX

This is a conditional reduction, not a proof of DRX. The canonical extension
algebra is constructed here. Two obligations remain:
existence of simple algebra-module targets of induction and the non-local
twisted dictionary.
The dictionary is the simple-object specialization of McRae, arXiv:1910.13226v2,
Theorem 4.15(1). It neither assumes `Nice` nor asserts positivity. HKL,
arXiv:1406.3420, Theorem 3.2/Remark 3.3 and Theorem 3.4, describes extensions
and local modules;
it is not by itself the non-local theorem. No cited result is declared an axiom.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos9
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open OrbPos2

section SimpleActions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A genuinely nonzero simple algebra module. Simplicity tests algebra-linear
monomorphisms, not all morphisms of the underlying category. -/
structure SimpleAction (A : C) [MonObj A] where
  obj : C
  act : A ⊗ obj ⟶ obj
  laws : IsLeftAct act
  nonzero : 𝟙 obj ≠ 0
  simple : ∀ (Y : C) (aY : A ⊗ Y ⟶ Y), IsLeftAct aY →
    ∀ f : Y ⟶ obj, IsLinear aY act f → Mono f → f = 0 ∨ IsIso f
end SimpleActions

/-- A monoid structure pinned to the actual ambient vertex operator and inclusion.
Commutativity is not needed by the free-module argument below. Existence is
proved below, rather than supplied as an assumed instance. -/
structure CanonicalExtensionAlgebra (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hSR : StronglyRational (orbifoldVOA G)) where
  monoid : letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    MonObj (ambient G)
  one_eq : letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := monoid
    (MonObj.one : vacuumObject ⟶ ambient G) = unitInclusion G
  mul_eq : letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := monoid
    (MonObj.mul : tensorObj (fusionChoice_pbw hSR) (ambient G) (ambient G) ⟶ ambient G) =
      ambientMultiplication G (fusionChoice_pbw hSR)

/-- The HKL extension-algebra construction, specialized to V₂.
The morphism and both unit laws have already been constructed in `OrbPos9Algebra`. -/
def ExceptionalExtensionAlgebraExists : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ hSR : StronglyRational (orbifoldVOA G), Nonempty (CanonicalExtensionAlgebra G hSR)

/-- After both unit laws, the remaining algebra-object law is this concrete
associativity equation for the canonical multiplication and Huang associator. -/
def ExceptionalExtensionAssociativity : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ hSR : StronglyRational (orbifoldVOA G),
      let F := fusionChoice_pbw hSR
      letI := monoidalCategoryOfStronglyRational_pbw F hSR
      let A := ambient G
      let m := ambientMultiplication G F
      (m ▷ A) ≫ m = (α_ A A A).hom ≫ (A ◁ m) ≫ m

/-- No additional algebra-object condition is hidden in the existence interface. -/
theorem exceptionalExtensionAlgebraExists_iff_associativity :
    ExceptionalExtensionAlgebraExists ↔ ExceptionalExtensionAssociativity := by
  constructor
  · intro h G hG hSR
    obtain ⟨E⟩ := h G hG hSR
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    simpa only [E.mul_eq] using MonObj.mul_assoc (ambient G)
  · intro h G hG hSR
    let F := fusionChoice_pbw hSR
    letI := monoidalCategoryOfStronglyRational_pbw F hSR
    let inst : MonObj (ambient G) :=
      { one := unitInclusion G
        mul := ambientMultiplication G F
        one_mul := ambientMultiplication_left_unit G F
        mul_one := ambientMultiplication_right_unit G F
        mul_assoc := h G hG hSR }
    exact ⟨⟨inst, rfl, rfl⟩⟩

/-- The actual multiplication is associative by ambient Jacobi and Huang's
four-point faithfulness over the strongly rational fixed algebra. -/
theorem exceptionalExtensionAssociativity_holds : ExceptionalExtensionAssociativity := by
  intro G _ hSR
  exact Assoc.act_assoc G (fusionChoice_pbw hSR) hSR

/-- The actual ambient VOA is an associative unital algebra object, under strong
rationality of the fixed algebra alone. -/
theorem exceptionalExtensionAlgebraExists : ExceptionalExtensionAlgebraExists :=
  exceptionalExtensionAlgebraExists_iff_associativity.mpr exceptionalExtensionAssociativity_holds

/-- The free unit for a pinned algebra is the explicitly split induction map. -/
theorem freeUnit_eq_inductionUnit (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)
    (X : Ordinary (orbifoldVOA G)) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    freeUnit (A := ambient G) X = inductionUnit G (fusionChoice_pbw hSR) X := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  change (leftUnitor (fusionChoice_pbw hSR) X).inv ≫
    tensorHom (fusionChoice_pbw hSR) MonObj.one (𝟙 X) = _
  rw [E.one_eq]
  rfl

/-- A simple target of a nonzero free algebra module. This is an algebraic
finite-length/simple-quotient obligation; it contains no twisted-module claim.
The use of a nonzero map is weaker than requiring a quotient map. -/
def ExceptionalFreeSimpleTargets : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ X : Ordinary (orbifoldVOA G), X.isMod.IsIrreducible →
        ∃ Q : SimpleAction (ambient G), ∃ q : ambient G ⊗ X ⟶ Q.obj,
          IsLinear (freeAction X) Q.act q ∧ q ≠ 0

/-- An entire ordinary U-module is the restriction of an irreducible sector.
The identity sector is represented by an ordinary V₂-module, exactly as in DRX. -/
def SectorRealization (G : Subgroup (Aut (V2m 1 le_rfl)))
    (Q : Ordinary (orbifoldVOA G)) : Prop :=
  (∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T)
      (P : OrdVModule (V2m 1 le_rfl) T), P.IsIrreducible ∧
    Nonempty (ModuleEquiv (orbifoldVOA G) Q.isMod ((orbifold G).restrictOrdVModule P))) ∨
  (∃ (g : G) (n : ℕ) (hn : 0 < n), orderOf g.1 = n ∧ g.1 ≠ 1 ∧
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module ℂ T)
      (P : TwistedModule g.1 n T), TwistedIrreducible P ∧
      Nonempty (ModuleEquiv (orbifoldVOA G) Q.isMod (orbifoldRestriction G g P hn)))

/-- The non-local dictionary, isolated from induction and positivity:
every simple module for the actual extension algebra underlies an irreducible
g-twisted V₂-module for some g in G. McRae Theorem 4.15(1), with simplicity
and restriction to the ordinary category; the identity sector is split off.
This is a literature-supported open proposition, NOT a theorem in this file. -/
def ExceptionalSimpleActionTwisted : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ Q : SimpleAction (ambient G), SectorRealization G Q.obj

/-- The categorical route implies the original, unchanged DRX disjunction.
All still-open construction and existence inputs appear as hypotheses. -/
theorem exceptionalDRXEmbedding_of_categorical
    (hAlg : ExceptionalExtensionAlgebraExists)
    (hTarget : ExceptionalFreeSimpleTargets)
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalDRXEmbedding := by
  intro G hG hSR M _ _ N hN
  obtain ⟨E⟩ := hAlg G hG hSR
  let F := fusionChoice_pbw hSR
  letI := monoidalCategoryOfStronglyRational_pbw F hSR
  letI := E.monoid
  let X := Ordinary.of N
  obtain ⟨Q, q, hq, hq0⟩ := hTarget G hG hSR E X hN
  let f : X ⟶ Q.obj := freeUnit X ≫ q
  have hfi : Function.Injective f.val := free_target_embedding F hSR
    (ambient G) X Q.obj hN Q.act q hq hq0
  rcases hTwisted G hG hSR E Q with h | h
  · obtain ⟨T, _, _, P, hP, ⟨e⟩⟩ := h
    refine Or.inl ⟨T, inferInstance, inferInstance, P, hP,
      e.toLinearEquiv.toLinearMap.comp f.val, ?_, e.toLinearEquiv.injective.comp hfi⟩
    intro v k x
    exact (congrArg e.toLinearEquiv (f.property v k x)).trans (e.map_act v k (f.val x))
  · obtain ⟨g, n, hn, ho, hg, T, _, _, P, hP, ⟨e⟩⟩ := h
    refine Or.inr ⟨g, n, hn, ho, hg, T, inferInstance, inferInstance, P, hP,
      e.toLinearEquiv.toLinearMap.comp f.val, ?_, e.toLinearEquiv.injective.comp hfi⟩
    intro v k x
    exact (congrArg e.toLinearEquiv (f.property v k x)).trans (e.map_act v k (f.val x))

/-- B5 from the explicit categorical obligations, with no `Nice U` hypothesis. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_categorical
    (hAlg : ExceptionalExtensionAlgebraExists)
    (hTarget : ExceptionalFreeSimpleTargets)
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalOrbifoldPositiveWeightsFact :=
  OrbPos8.exceptionalOrbifoldPositiveWeightsFact_of_drx
    (exceptionalDRXEmbedding_of_categorical hAlg hTarget hTwisted)

/-- Session-nine endpoint: only simple-target existence and the non-local
simple-action dictionary remain. The original DRX statement is unchanged. -/
theorem exceptionalDRXEmbedding_of_simple_targets_twisted
    (hTarget : ExceptionalFreeSimpleTargets)
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalDRXEmbedding :=
  exceptionalDRXEmbedding_of_categorical exceptionalExtensionAlgebraExists hTarget hTwisted

/-- B5 from the two explicit remaining categorical propositions. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_simple_targets_twisted
    (hTarget : ExceptionalFreeSimpleTargets)
    (hTwisted : ExceptionalSimpleActionTwisted) : ExceptionalOrbifoldPositiveWeightsFact :=
  OrbPos8.exceptionalOrbifoldPositiveWeightsFact_of_drx
    (exceptionalDRXEmbedding_of_simple_targets_twisted hTarget hTwisted)

end VOA.Classification.COne.OrbPos9
