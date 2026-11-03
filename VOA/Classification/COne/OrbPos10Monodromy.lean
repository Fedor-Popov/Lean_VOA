import VOA.Classification.COne.OrbPos10Targets

/-! # The precise monodromy and twisted-field obligations

The equation below is McRae, arXiv:1910.13226v2, Definition 2.3,
with categorical composition written from left to right. The existence of its
G-label on a simple action is the categorical part of Theorem 4.15(1).
The conversion to twisted VOA fields is a separate issue (Theorem 4.14).
Both are open propositions here, not asserted theorems or axioms.

In particular, monodromy followed by the action is a map A ⊗ X → X,
not an endomorphism of X. Schur's lemma alone does not prove this equation.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos10
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open CategoryTheory MonoidalCategory OrbPos9 OrbPos2 BraidRibbon
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The actual G-action on the ambient ordinary fixed-algebra module. -/
def ambientSymmetry (G : Subgroup (Aut W)) (g : G) : ambient G ≅ ambient G :=
  Ordinary.isoOfModuleEquiv
    { toLinearEquiv := g.1.toLinearEquiv
      map_act := fun a n x => by
        change g.1 (W.smul a.1 n x) = W.smul a.1 n (g.1 x)
        rw [g.1.map_smul', a.2 g.1 g.2] }

@[simp] theorem ambientSymmetry_apply (G : Subgroup (Aut W)) (g : G) (x : V) :
    (ambientSymmetry G g).hom.val x = g.1 x := rfl

/-- Every G-symmetry fixes the actual inclusion of the fixed algebra. -/
theorem ambientSymmetry_unit (G : Subgroup (Aut W)) (g : G) :
    unitInclusion G ≫ (ambientSymmetry G g).hom = unitInclusion G := by
  apply Ordinary.hom_ext
  intro a
  exact a.2 g.1 g.2

/-- Every G-symmetry preserves the actual ambient vertex-operator multiplication. -/
theorem ambientSymmetry_mul (G : Subgroup (Aut W)) (g : G)
    (F : FusionChoice (orbifoldVOA G)) :
    tensorHom F (ambientSymmetry G g).hom (ambientSymmetry G g).hom ≫
        ambientMultiplication G F =
      ambientMultiplication G F ≫ (ambientSymmetry G g).hom := by
  apply tensor_hom_ext F
  intro n a b
  rw [Ordinary.comp_apply, Ordinary.comp_apply, tensorHom_intertwiner,
    ambientMultiplication_intertwiner, ambientMultiplication_intertwiner]
  simp only [ambientSymmetry_apply]
  unfold moduleModes
  split_ifs
  · exact (g.1.map_smul' a _ b).symm
  · simp

/-- The action respects the pinned monoid structure, not merely an unspecified
algebra structure on the same underlying object. -/
theorem ambientSymmetry_isMonHom
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) (g : G) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    IsMonHom (ambientSymmetry G g).hom := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  constructor
  · rw [E.one_eq]
    exact ambientSymmetry_unit G g
  · rw [E.mul_eq]
    exact (ambientSymmetry_mul G g _).symm

/-- Categorical g-twistedness, using the actual Huang braiding and actual G-action.
The maps on both sides have domain A ⊗ X and codomain X. -/
def ActionMonodromyThrough
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X) (g : G) : Prop :=
  let F := fusionChoice_pbw hSR
  (braiding F (ambient G) X).hom ≫ (braiding F X (ambient G)).hom ≫
    tensorHom F (ambientSymmetry G g).hom (𝟙 X) ≫ a = a

set_option maxHeartbeats 1000000 in
-- Unfolding the concrete lattice carrier in scalar-map compatibility is expensive.
/-- The categorical monodromy condition is exactly the phase/covariance identity
on every universal intertwiner coefficient. This keeps the analytic-to-formal
support step available without identifying monodromy with an endomorphism of X. -/
theorem actionMonodromyThrough_iff_coefficients
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X) (g : G) :
    ActionMonodromyThrough G hSR X a g ↔
      ∀ (n : ℂ) (v : (ambient G).carrier) (x : X.carrier),
        (Phase.upper.c n * Phase.upper.c n) •
          a.val (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val n (g.1 v) x) =
        a.val (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val n v x) := by
  let F := fusionChoice_pbw hSR
  have hc (n : ℂ) (v : (ambient G).carrier) (x : X.carrier) :
      ((braiding F (ambient G) X).hom ≫ (braiding F X (ambient G)).hom ≫
        tensorHom F (ambientSymmetry G g).hom (𝟙 X) ≫ a).val
          ((F (ambient G) X).intertwiner.val n v x) =
        (Phase.upper.c n * Phase.upper.c n) •
          a.val ((F (ambient G) X).intertwiner.val n (g.1 v) x) := by
    change a.val ((tensorHom F (ambientSymmetry G g).hom (𝟙 X)).val
      (((braiding F (ambient G) X).hom ≫ (braiding F X (ambient G)).hom).val
        ((F (ambient G) X).intertwiner.val n v x))) = _
    rw [braidingP_monodromy Phase.upper F (ambient G) X n v x]
    erw [map_smul, map_smul, tensorHom_intertwiner, Ordinary.id_apply]
  constructor
  · intro h n v x
    have he := congrArg (fun f => f.val ((F (ambient G) X).intertwiner.val n v x)) h
    exact (hc n v x).symm.trans he
  · intro h
    apply tensor_hom_ext F
    intro n v x
    exact (hc n v x).trans (h n v x)

/-- OPEN: monodromy of every simple extension action is accounted for by an
actual element of G. This contains no twisted-VOA or positivity conclusion. -/
def ExceptionalSimpleActionMonodromy : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ Q : SimpleAction (ambient G), ∃ g : G, ActionMonodromyThrough G hSR Q.obj Q.act g

/-- OPEN: the twisted-field dictionary restricted to actions already satisfying
categorical g-twistedness. The conclusion is the unchanged sector interface;
it does not pin a sign convention for the sector label. This is separate from
the existence of the monodromy label. -/
def ExceptionalMonodromySectorDictionary : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ (Q : SimpleAction (ambient G)) (g : G),
        ActionMonodromyThrough G hSR Q.obj Q.act g → SectorRealization G Q.obj

/-- The full simple-action dictionary implies its explicitly restricted version. -/
theorem monodromySectorDictionary_of_simpleActionTwisted
    (h : ExceptionalSimpleActionTwisted) : ExceptionalMonodromySectorDictionary := by
  intro G hG hSR E Q _ _
  exact h G hG hSR E Q

/-- Both unproved parts are displayed: categorical label existence and the
VOA twisted-field dictionary. No claim that monodromy alone closes DRX is made. -/
theorem exceptionalSimpleActionTwisted_of_monodromy_dictionary
    (hM : ExceptionalSimpleActionMonodromy)
    (hD : ExceptionalMonodromySectorDictionary) : ExceptionalSimpleActionTwisted := by
  intro G hG hSR E Q
  obtain ⟨g, hg⟩ := hM G hG hSR E Q
  exact hD G hG hSR E Q g hg

/-- DRX with simple-target existence discharged. -/
theorem exceptionalDRXEmbedding_of_monodromy_dictionary
    (hM : ExceptionalSimpleActionMonodromy)
    (hD : ExceptionalMonodromySectorDictionary) : ExceptionalDRXEmbedding :=
  exceptionalDRXEmbedding_of_simpleActionTwisted
    (exceptionalSimpleActionTwisted_of_monodromy_dictionary hM hD)

/-- The unchanged B5 target with both remaining sub-obligations explicit. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_monodromy_dictionary
    (hM : ExceptionalSimpleActionMonodromy)
    (hD : ExceptionalMonodromySectorDictionary) : ExceptionalOrbifoldPositiveWeightsFact :=
  OrbPos8.exceptionalOrbifoldPositiveWeightsFact_of_drx
    (exceptionalDRXEmbedding_of_monodromy_dictionary hM hD)

end VOA.Classification.COne.OrbPos10
