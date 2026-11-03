import VOA.Huang.TensorCatEvaluation

/-! # Natural representability bridge

Faithful ordinary scalar evaluations with the same range give an associator
natural in all four modules. The input naturality is a theorem, not an extra
field of the analytic input. The three analytic predicates are not discharged
from strong rationality in this file.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- All analytic obligations for the concrete ordinary four-point evaluation.
None of the fields assumes a comparison, naturality, or monoidal coherence. -/
structure OrdinaryFourPointInput : Prop where
  summability : OrdinaryFourPointSummability F
  faithfulness : OrdinaryFourPointFaithfulness F
  range_eq : OrdinaryFourPointRangeEquality F

variable (H : OrdinaryFourPointInput F)

/-- Transport through the common space of actual scalar functions. -/
def ordinaryFourPointCompare (X Y Z T : Ordinary W) :
    IterateSpace F X Y Z T ≃ₗ[ℂ] ProductSpace F X Y Z T :=
  (LinearEquiv.ofInjective (iterateEvaluationLinear F H.summability X Y Z T)
    (H.faithfulness X Y Z T).1).trans
    ((LinearEquiv.ofEq _ _ (SetLike.coe_injective (H.range_eq X Y Z T))).trans
      (LinearEquiv.ofInjective (productEvaluationLinear F H.summability X Y Z T)
        (H.faithfulness X Y Z T).2).symm)

/-- The comparison preserves every real-overlap matrix coefficient. -/
theorem ordinaryFourPointCompare_spec (X Y Z T : Ordinary W)
    (I : IterateSpace F X Y Z T) :
    productEvaluation F (ordinaryFourPointCompare F H X Y Z T I) =
      iterateEvaluation F I := by
  let e := LinearEquiv.ofInjective (productEvaluationLinear F H.summability X Y Z T)
    (H.faithfulness X Y Z T).2
  have he := e.apply_symm_apply
    ((LinearEquiv.ofEq _ _ (SetLike.coe_injective (H.range_eq X Y Z T)))
      (LinearEquiv.ofInjective (iterateEvaluationLinear F H.summability X Y Z T)
        (H.faithfulness X Y Z T).1 I))
  exact congrArg Subtype.val he

/-- Output naturality follows by pulling back the supported functional. -/
theorem ordinaryFourPointCompare_output {X Y Z T U : Ordinary W}
    (I : IterateSpace F X Y Z T) (f : T ⟶ U) :
    ordinaryFourPointCompare F H X Y Z U (postcompose I U.isMod f) =
      postcompose (ordinaryFourPointCompare F H X Y Z T I) U.isMod f := by
  apply (H.faithfulness X Y Z U).2
  funext d
  rw [ordinaryFourPointCompare_spec]
  rw [iterateEvaluation_output, productEvaluation_output]
  exact congrFun (ordinaryFourPointCompare_spec F H X Y Z T I).symm (d.output f)

/-- All three input naturality laws follow by pushing forward the test vectors. -/
theorem ordinaryFourPointCompare_inputs {X Y Z X' Y' Z' T : Ordinary W}
    (I : IterateSpace F X' Y' Z' T)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ordinaryFourPointCompare F H X Y Z T (restrictInputs (tensorHom F f g) h I) =
      restrictInputs f (tensorHom F g h) (ordinaryFourPointCompare F H X' Y' Z' T I) := by
  apply (H.faithfulness X Y Z T).2
  funext d
  rw [ordinaryFourPointCompare_spec]
  rw [iterateEvaluation_inputs, productEvaluation_inputs]
  exact congrFun (ordinaryFourPointCompare_spec F H X' Y' Z' T I).symm (d.inputs f g h)

/-- A family of reassociations with the full input naturality square. -/
structure NaturalReassociation where
  reassociation : ∀ X Y Z : Ordinary W, Reassociation F X Y Z
  inputs {X Y Z X' Y' Z' T : Ordinary W}
    (I : IterateSpace F X' Y' Z' T) (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (reassociation X Y Z).compare T (restrictInputs (tensorHom F f g) h I) =
      restrictInputs f (tensorHom F g h) ((reassociation X' Y' Z').compare T I)

/-- Concrete scalar evaluation supplies both naturality directions. -/
def naturalReassociationOfEvaluation : NaturalReassociation F where
  reassociation X Y Z :=
    { compare := ordinaryFourPointCompare F H X Y Z
      natural := ordinaryFourPointCompare_output F H }
  inputs := ordinaryFourPointCompare_inputs F H

/-- The original naturality input follows from the concrete analytic obligations. -/
theorem reassociationInput_of_evaluation (H : OrdinaryFourPointInput F) : ReassociationInput F :=
  fun X Y Z => ⟨(naturalReassociationOfEvaluation F H).reassociation X Y Z⟩

variable {F}

/-- Compatibility of representability with the supplied comparison. -/
theorem Reassociation.homEquiv_spec {X Y Z : Ordinary W} (R : Reassociation F X Y Z)
    (T : Ordinary W) (f : tensorObj F (tensorObj F X Y) Z ⟶ T) :
    postcompose (F X (tensorObj F Y Z)).intertwiner T.isMod (R.homEquiv T f) =
      R.compare T (postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod f) :=
  (FusionProduct.homEquiv
    ((F X (tensorObj F Y Z)).universal T.carrier T.isMod)).apply_symm_apply _

variable (R : NaturalReassociation F)

/-- Input naturality transported to the represented Hom equivalences. -/
theorem NaturalReassociation.homEquiv_inputs {X Y Z X' Y' Z' T : Ordinary W}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (k : tensorObj F (tensorObj F X' Y') Z' ⟶ T) :
    (R.reassociation X Y Z).homEquiv T (tensorHom F (tensorHom F f g) h ≫ k) =
      tensorHom F f (tensorHom F g h) ≫ (R.reassociation X' Y' Z').homEquiv T k := by
  apply (F X (tensorObj F Y Z)).universal T.carrier T.isMod |>.1
  rw [Reassociation.homEquiv_spec]
  have hl : postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod
      (tensorHom F (tensorHom F f g) h ≫ k) =
      restrictInputs (tensorHom F f g) h
        (postcompose (F (tensorObj F X' Y') Z').intertwiner T.isMod k) := by
    apply Subtype.ext
    funext n
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    change k.val ((tensorHom F (tensorHom F f g) h).val _) = _
    rw [tensorHom_intertwiner]
    rfl
  rw [hl, R.inputs]
  rw [← Reassociation.homEquiv_spec]
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  change _ = ((R.reassociation X' Y' Z').homEquiv T k).val
    ((tensorHom F f (tensorHom F g h)).val _)
  rw [tensorHom_intertwiner]
  rfl

/-- The associator family coming from a natural comparison. -/
def NaturalReassociation.associators : AssociatorFamily F :=
  fun X Y Z => (R.reassociation X Y Z).associator

theorem NaturalReassociation.inv_naturality {X Y Z X' Y' Z' : Ordinary W}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (R.associators X Y Z).inv ≫ tensorHom F (tensorHom F f g) h =
      tensorHom F f (tensorHom F g h) ≫ (R.associators X' Y' Z').inv := by
  have hh := R.homEquiv_inputs f g h (𝟙 (tensorObj F (tensorObj F X' Y') Z'))
  rw [Category.comp_id, Reassociation.homEquiv_eq_precompose] at hh
  exact hh

/-- Naturality of the actual module associator, with no extra naturality input. -/
theorem NaturalReassociation.associator_naturality {X Y Z X' Y' Z' : Ordinary W}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tensorHom F (tensorHom F f g) h ≫ (R.associators X' Y' Z').hom =
      (R.associators X Y Z).hom ≫ tensorHom F f (tensorHom F g h) := by
  calc
    _ = (R.associators X Y Z).hom ≫
        ((R.associators X Y Z).inv ≫ tensorHom F (tensorHom F f g) h) ≫
          (R.associators X' Y' Z').hom := by simp
    _ = _ := by rw [R.inv_naturality]; simp

end VOA.Huang.TensorCat
