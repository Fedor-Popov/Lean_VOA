/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.Rename
import VOA.Commutative.LiteralSubstitutionNewton
import VOA.Commutative.RootedIncidenceAction

/-!
# A finite scalar-polynomial evaluator for the boundary affine incidence model

This file constructs the model-independent scalar-polynomial part of the proposed `p = 3`
functional model.  A variable is attached to each labelled current or `S` source.  A rooted
matching evaluates that variable at the variable of its block root, and an incidence lift then
renames the root variable by its colored slot.  Thus all labels in one rooted block are literally
identified.

Species-preserving source relabeling acts by renaming source variables.  The incidence evaluator
is covariant for the source groupoid, and hence its value on a source-invariant polynomial
descends to the realized exact root-type assignment.  Composing with `literalSubstitution`
supplies the corresponding one-variable diagonal-offset evaluation.

This is deliberately not the full `p = 3` functional model.  In particular, it does not construct
the restricted-dual-to-polynomial realization, the coupled `X/Y/Z/S` polarization, the quadric
relation, a cone carrier, a common-factor theorem, a Hilbert series, or classical freeness.  The
structure `InvariantScalarPolynomialRealization` below records the precise additional map which a
concrete restricted-dual model must supply before the generic descent theorem applies.
-/

namespace VOA.P3FunctionalModel

open VOA.RootedMatching

noncomputable section

universe u v w x

variable {C : Type u} {S : Type v} {A : Type w}
variable {R : Type x} [CommSemiring R]

/-- The three current polarizations used in the scalar shadow of the `p = 3` affine model. -/
inductive CurrentSpecies where
  | X
  | Y
  | Z
  deriving DecidableEq

instance : Fintype CurrentSpecies where
  elems := {CurrentSpecies.X, CurrentSpecies.Y, CurrentSpecies.Z}
  complete a := by cases a <;> simp

/-- A finite set of labelled currents with a prescribed multiplicity for each polarization. -/
abbrev CurrentLabels (multiplicity : CurrentSpecies → ℕ) :=
  Σ a : CurrentSpecies, Fin (multiplicity a)

/-- Forget the label of a current and retain its `X`, `Y`, or `Z` species. -/
def currentSpecies (multiplicity : CurrentSpecies → ℕ) :
    CurrentLabels multiplicity → CurrentSpecies :=
  Sigma.fst

/-- The finite scalar polynomial ring with prescribed numbers of `X`, `Y`, `Z`, and `S`
labels.  This is a labelled source space, not yet the quadric-cone carrier. -/
abbrev ScalarPolynomial (multiplicity : CurrentSpecies → ℕ) (sCount : ℕ)
    (R : Type x) [CommSemiring R] :=
  MvPolynomial (Root (CurrentLabels multiplicity) (Fin sCount)) R

/-- Species-preserving relabelings of the finite `p = 3` scalar source labels. -/
abbrev SourcePermutationGroup (multiplicity : CurrentSpecies → ℕ) (sCount : ℕ) :=
  SourceRelabeling (S := Fin sCount) (currentSpecies multiplicity)

/-- Scalar polynomials in finitely many labelled current and `S` particle variables.

When `C` and `S` are finite, the variable type is finite.  No finite-dimensional degree cutoff is
imposed on the polynomial ring. -/
abbrev LabelledParticlePolynomial (C : Type u) (S : Type v) (R : Type x)
    [CommSemiring R] :=
  MvPolynomial (Root C S) R

/-- The root of the block containing a source label, regarded as an element of the root subtype. -/
def centerRoot (m : RawRootedMatching C S) (x : Root C S) : MatchingRoots m :=
  ⟨m.center x, m.center_isRoot x⟩

@[simp]
theorem centerRoot_val (m : RawRootedMatching C S) (x : Root C S) :
    (centerRoot m x).1 = m.center x :=
  rfl

/-- Literal rooted evaluation: identify every labelled variable with the variable of its block
root. -/
def rootedEvaluation (m : RawRootedMatching C S) :
    MvPolynomial (Root C S) R →ₐ[R] MvPolynomial (MatchingRoots m) R :=
  MvPolynomial.rename (centerRoot m)

@[simp]
theorem rootedEvaluation_X (m : RawRootedMatching C S) (x : Root C S) :
    rootedEvaluation (R := R) m (MvPolynomial.X x) =
      MvPolynomial.X (centerRoot m x) :=
  MvPolynomial.rename_X _ _

section Incidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}

/-- The colored slot occupied by the root of the block containing a source label. -/
def slotOfLabel (I : RootedIncidence hn rho) (x : Root C S) :
    ColoredSlots (rho : Fin n → ℕ) :=
  I.rootToSlot (centerRoot I.matching.1.1 x)

/-- Evaluate each labelled source variable at the variable of the colored slot occupied by its
block root. -/
def incidenceEvaluation (I : RootedIncidence hn rho) :
    MvPolynomial (Root C S) R →ₐ[R]
      MvPolynomial (ColoredSlots (rho : Fin n → ℕ)) R :=
  MvPolynomial.rename (slotOfLabel I)

@[simp]
theorem incidenceEvaluation_X (I : RootedIncidence hn rho) (x : Root C S) :
    incidenceEvaluation (R := R) I (MvPolynomial.X x) =
      MvPolynomial.X (slotOfLabel I x) :=
  MvPolynomial.rename_X _ _

/-- Incidence evaluation factors through rooted evaluation and then the root-to-slot
equivalence. -/
theorem incidenceEvaluation_factorization (I : RootedIncidence hn rho) :
    (MvPolynomial.rename (R := R) I.rootToSlot).comp
        (rootedEvaluation (R := R) I.matching.1.1) =
      incidenceEvaluation (R := R) I := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.coe_comp, Function.comp_apply, rootedEvaluation_X,
    incidenceEvaluation_X, MvPolynomial.rename_X]
  rfl

omit [Finite C] [Finite S] in
/-- Two rooted evaluations agree after coordinate change as soon as the two coordinate maps
agree on the center of every labelled source particle.  This is the algebraic core of literal
endpoint compatibility: after a reassignment or absorption, the model-specific proof only has
to check the corresponding equality of center coordinates on generators. -/
theorem rootedEvaluation_coordinateChange
    (m m' : RawRootedMatching C S) {T : Type*}
    (f : MatchingRoots m → T) (f' : MatchingRoots m' → T)
    (hcenter : ∀ x : Root C S, f (centerRoot m x) = f' (centerRoot m' x)) :
    (MvPolynomial.rename (R := R) f).comp (rootedEvaluation (R := R) m) =
      (MvPolynomial.rename (R := R) f').comp (rootedEvaluation (R := R) m') := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.coe_comp, Function.comp_apply, rootedEvaluation_X,
    MvPolynomial.rename_X]
  rw [hcenter x]

/-- The polynomial renaming induced by a species-preserving source relabeling. -/
def relabelPolynomial (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) :
    MvPolynomial (Root C S) R →ₐ[R] MvPolynomial (Root C S) R :=
  MvPolynomial.rename (g.sumEquiv currentType)

omit [Finite C] [Finite S] in
@[simp]
theorem relabelPolynomial_one (currentType : C → A)
    (p : MvPolynomial (Root C S) R) :
    relabelPolynomial (R := R) currentType 1 p = p := by
  rw [relabelPolynomial, SourceRelabeling.sumEquiv_one]
  exact MvPolynomial.rename_id_apply p

omit [Finite C] [Finite S] in
@[simp]
theorem relabelPolynomial_mul (currentType : C → A)
    (g h : SourceRelabeling (S := S) currentType)
    (p : MvPolynomial (Root C S) R) :
    relabelPolynomial (R := R) currentType (g * h) p =
      relabelPolynomial (R := R) currentType g
        (relabelPolynomial (R := R) currentType h p) := by
  rw [relabelPolynomial, SourceRelabeling.sumEquiv_mul]
  change MvPolynomial.rename
      (fun x => g.sumEquiv currentType (h.sumEquiv currentType x)) p = _
  exact (MvPolynomial.rename_rename _ _ p).symm

/-- The strict source-permutation action on labelled scalar polynomials. -/
@[reducible]
def sourceMulActionPolynomial (currentType : C → A) :
    MulAction (SourceRelabeling (S := S) currentType)
      (MvPolynomial (Root C S) R) where
  smul g p := relabelPolynomial (R := R) currentType g p
  one_smul := relabelPolynomial_one currentType
  mul_smul := relabelPolynomial_mul currentType

omit [Finite C] [Finite S] in
/-- Rooted evaluation is covariant under the source action.  The target root variables are
renamed by the induced equivalence of root subtypes. -/
theorem rootedEvaluation_relabel_comp (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S) :
    (rootedEvaluation (R := R) (relabelRaw currentType g m)).comp
        (relabelPolynomial (R := R) currentType g) =
      (MvPolynomial.rename (R := R) (relabelRootEquiv currentType g m)).comp
        (rootedEvaluation (R := R) m) := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.coe_comp, Function.comp_apply, rootedEvaluation_X,
    relabelPolynomial, MvPolynomial.rename_X]
  apply congrArg MvPolynomial.X
  apply Subtype.ext
  exact relabelRaw_center currentType g m x

/-- The explicitly relabeled incidence has exactly the same slot evaluation after its source
variables are relabeled. -/
theorem incidenceEvaluation_relabel_comp (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (I : RootedIncidence hn rho) :
    (incidenceEvaluation (R := R) (I.relabel currentType g)).comp
        (relabelPolynomial (R := R) currentType g) =
      incidenceEvaluation (R := R) I := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.coe_comp, Function.comp_apply, incidenceEvaluation_X,
    relabelPolynomial, MvPolynomial.rename_X]
  apply congrArg MvPolynomial.X
  change I.rootToSlot
      ((relabelRootEquiv currentType g I.matching.1.1).symm
        (centerRoot (relabelRaw currentType g I.matching.1.1)
          (g.sumEquiv currentType x))) =
    I.rootToSlot (centerRoot I.matching.1.1 x)
  apply congrArg I.rootToSlot
  apply (relabelRootEquiv currentType g I.matching.1.1).injective
  rw [(relabelRootEquiv currentType g I.matching.1.1).apply_symm_apply]
  apply Subtype.ext
  exact relabelRaw_center currentType g I.matching.1.1 x

/-- A source translation sends the slot of every relabeled source to its original slot. -/
theorem slotOfLabel_eq_of_isSourceTranslate (currentType : C → A)
    {g : SourceRelabeling (S := S) currentType}
    {I J : RootedIncidence hn rho}
    (h : RootedIncidence.IsSourceTranslate currentType g I J)
    (x : Root C S) :
    slotOfLabel J (g.sumEquiv currentType x) = slotOfLabel I x := by
  let r : MatchingRoots I.matching.1.1 := centerRoot I.matching.1.1 x
  let E := rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1
    g.1.1 g.2 h.center
  have hroot : centerRoot J.matching.1.1 (g.sumEquiv currentType x) = E r := by
    apply Subtype.ext
    exact (h.center x).symm
  change J.rootToSlot (centerRoot J.matching.1.1 (g.sumEquiv currentType x)) =
    I.rootToSlot r
  rw [hroot]
  exact h.slots r

/-- Covariance for an arbitrary edge of the source-action groupoid. -/
theorem incidenceEvaluation_sourceTranslate_comp (currentType : C → A)
    {g : SourceRelabeling (S := S) currentType}
    {I J : RootedIncidence hn rho}
    (h : RootedIncidence.IsSourceTranslate currentType g I J) :
    (incidenceEvaluation (R := R) J).comp
        (relabelPolynomial (R := R) currentType g) =
      incidenceEvaluation (R := R) I := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.coe_comp, Function.comp_apply, incidenceEvaluation_X,
    relabelPolynomial, MvPolynomial.rename_X]
  rw [slotOfLabel_eq_of_isSourceTranslate currentType h x]

/-- A labelled polynomial is source invariant when every species-preserving relabeling fixes it. -/
def IsSourceInvariant (currentType : C → A)
    (p : MvPolynomial (Root C S) R) : Prop :=
  ∀ g : SourceRelabeling (S := S) currentType,
    relabelPolynomial (R := R) currentType g p = p

/-- The source-invariant scalar-polynomial sector. -/
abbrev SourceInvariantPolynomial (currentType : C → A) :=
  {p : MvPolynomial (Root C S) R // IsSourceInvariant (R := R) currentType p}

/-- Incidence evaluation of a source-invariant polynomial is constant across every source
translation. -/
theorem incidenceEvaluation_eq_of_isSourceTranslate (currentType : C → A)
    {g : SourceRelabeling (S := S) currentType}
    {I J : RootedIncidence hn rho}
    (h : RootedIncidence.IsSourceTranslate currentType g I J)
    {p : MvPolynomial (Root C S) R}
    (hp : IsSourceInvariant (R := R) currentType p) :
    incidenceEvaluation (R := R) I p = incidenceEvaluation (R := R) J p := by
  calc
    incidenceEvaluation (R := R) I p =
        incidenceEvaluation (R := R) J
          (relabelPolynomial (R := R) currentType g p) :=
      (DFunLike.congr_fun
        (incidenceEvaluation_sourceTranslate_comp (R := R) currentType h) p).symm
    _ = incidenceEvaluation (R := R) J p := congrArg _ (hp g)

/-- The incidence evaluation of a source-invariant polynomial is constant on exact-assignment
fibers. -/
theorem incidenceEvaluation_isFiberConstant (currentType : C → A)
    {p : MvPolynomial (Root C S) R}
    (hp : IsSourceInvariant (R := R) currentType p) :
    OrbitEvaluationDescent.IsFiberConstant
      (RootedIncidence.exactAssignmentMap (hn := hn) (rho := rho) currentType)
      (fun I : RootedIncidence hn rho => incidenceEvaluation (R := R) I p) := by
  apply RootedIncidence.isFiberConstant_exactAssignmentMap_of_source_invariant
    currentType
  intro g I J h
  exact incidenceEvaluation_eq_of_isSourceTranslate currentType h hp

/-- Lift-independent slot-polynomial evaluation indexed by realized exact assignments. -/
def descendedIncidenceEvaluation (currentType : C → A)
    (p : SourceInvariantPolynomial (R := R) (S := S) currentType) :
    RootedIncidence.RealizedAssignments (hn := hn) (rho := rho) currentType →
      MvPolynomial (ColoredSlots (rho : Fin n → ℕ)) R :=
  OrbitEvaluationDescent.descendedValue
    (RootedIncidence.exactAssignmentMap (hn := hn) (rho := rho) currentType)
    (RootedIncidence.exactAssignmentMap_surjective (hn := hn) (rho := rho) currentType)
    (fun I : RootedIncidence hn rho => incidenceEvaluation (R := R) I p.1)

@[simp]
theorem descendedIncidenceEvaluation_exactAssignmentMap (currentType : C → A)
    (p : SourceInvariantPolynomial (R := R) (S := S) currentType)
    (I : RootedIncidence hn rho) :
    descendedIncidenceEvaluation (hn := hn) (rho := rho) currentType p
        (RootedIncidence.exactAssignmentMap currentType I) =
      incidenceEvaluation (R := R) I p.1 := by
  apply OrbitEvaluationDescent.descendedValue_theta
  exact incidenceEvaluation_isFiberConstant currentType p.2

local instance : DecidableEq (ColoredSlots (rho : Fin n → ℕ)) := Classical.decEq _

/-- One-variable diagonal-offset evaluation after the rooted incidence substitution. -/
def literalRootedEvaluation (I : RootedIncidence hn rho)
    (T : Finset (ColoredSlots (rho : Fin n → ℕ))) :
    MvPolynomial (Root C S) R →+* Polynomial R :=
  (LiteralSubstitutionNewton.literalSubstitution T).comp
    (incidenceEvaluation (R := R) I).toRingHom

@[simp]
theorem literalRootedEvaluation_X (I : RootedIncidence hn rho)
    (T : Finset (ColoredSlots (rho : Fin n → ℕ))) (x : Root C S) :
    literalRootedEvaluation (R := R) I T (MvPolynomial.X x) =
      if slotOfLabel I x ∈ T then Polynomial.X else 0 := by
  simp [literalRootedEvaluation, LiteralSubstitutionNewton.literalSubstitution]

/-- Literal diagonal-offset evaluation inherits source covariance. -/
theorem literalRootedEvaluation_sourceTranslate (currentType : C → A)
    {g : SourceRelabeling (S := S) currentType}
    {I J : RootedIncidence hn rho}
    (h : RootedIncidence.IsSourceTranslate currentType g I J)
    (T : Finset (ColoredSlots (rho : Fin n → ℕ)))
    (p : MvPolynomial (Root C S) R) :
    literalRootedEvaluation (R := R) J T
        (relabelPolynomial (R := R) currentType g p) =
      literalRootedEvaluation (R := R) I T p := by
  change LiteralSubstitutionNewton.literalSubstitution T
      (incidenceEvaluation (R := R) J
        (relabelPolynomial (R := R) currentType g p)) =
    LiteralSubstitutionNewton.literalSubstitution T
      (incidenceEvaluation (R := R) I p)
  exact congrArg (LiteralSubstitutionNewton.literalSubstitution T)
    (DFunLike.congr_fun
      (incidenceEvaluation_sourceTranslate_comp (R := R) currentType h) p)

/-- Literal evaluation of a source-invariant polynomial is constant on exact-assignment fibers. -/
theorem literalRootedEvaluation_isFiberConstant (currentType : C → A)
    (T : Finset (ColoredSlots (rho : Fin n → ℕ)))
    {p : MvPolynomial (Root C S) R}
    (hp : IsSourceInvariant (R := R) currentType p) :
    OrbitEvaluationDescent.IsFiberConstant
      (RootedIncidence.exactAssignmentMap (hn := hn) (rho := rho) currentType)
      (fun I : RootedIncidence hn rho => literalRootedEvaluation (R := R) I T p) := by
  apply RootedIncidence.isFiberConstant_exactAssignmentMap_of_source_invariant
    currentType
  intro g I J h
  calc
    literalRootedEvaluation (R := R) I T p =
        literalRootedEvaluation (R := R) J T
          (relabelPolynomial (R := R) currentType g p) :=
      (literalRootedEvaluation_sourceTranslate currentType h T p).symm
    _ = literalRootedEvaluation (R := R) J T p := congrArg _ (hp g)

section ModelInstantiation

variable {V : Type*} [AddCommMonoid V] [Module R V]

/-- Precise generic input required from a concrete invariant functional model: a linear
realization by labelled scalar polynomials, together with source invariance of every realized
polynomial.  The `p = 3` restricted-dual construction has not yet been instantiated here. -/
structure InvariantScalarPolynomialRealization (currentType : C → A) where
  toPolynomial : V →ₗ[R] MvPolynomial (Root C S) R
  source_invariant : ∀ (g : SourceRelabeling (S := S) currentType) (v : V),
    relabelPolynomial (R := R) currentType g (toPolynomial v) = toPolynomial v

namespace InvariantScalarPolynomialRealization

/-- Evaluate a concrete invariant scalar-polynomial realization at a labelled incidence. -/
def incidenceEval (currentType : C → A)
    (M : InvariantScalarPolynomialRealization (R := R) (S := S) (V := V) currentType)
    (I : RootedIncidence hn rho) :
    V →ₗ[R] MvPolynomial (ColoredSlots (rho : Fin n → ℕ)) R :=
  (incidenceEvaluation (R := R) I).toLinearMap.comp M.toPolynomial

/-- The concrete incidence evaluation family is constant on exact-assignment fibers. -/
theorem incidenceEval_isFiberConstant (currentType : C → A)
    (M : InvariantScalarPolynomialRealization (R := R) (S := S) (V := V) currentType) :
    OrbitEvaluationDescent.IsFiberConstant
      (RootedIncidence.exactAssignmentMap (hn := hn) (rho := rho) currentType)
      (fun I : RootedIncidence hn rho => M.incidenceEval currentType I) := by
  apply RootedIncidence.isFiberConstant_exactAssignmentMap_of_source_invariant
    currentType
  intro g I J h
  apply LinearMap.ext
  intro v
  change incidenceEvaluation (R := R) I (M.toPolynomial v) =
    incidenceEvaluation (R := R) J (M.toPolynomial v)
  calc
    incidenceEvaluation (R := R) I (M.toPolynomial v) =
        incidenceEvaluation (R := R) J
          (relabelPolynomial (R := R) currentType g (M.toPolynomial v)) :=
      (DFunLike.congr_fun
        (incidenceEvaluation_sourceTranslate_comp (R := R) currentType h)
        (M.toPolynomial v)).symm
    _ = incidenceEvaluation (R := R) J (M.toPolynomial v) :=
      congrArg _ (M.source_invariant g v)

/-- Descend a concrete invariant scalar-polynomial realization to realized exact assignments. -/
def descendedEval (currentType : C → A)
    (M : InvariantScalarPolynomialRealization (R := R) (S := S) (V := V) currentType) :
    RootedIncidence.RealizedAssignments (hn := hn) (rho := rho) currentType →
      V →ₗ[R] MvPolynomial (ColoredSlots (rho : Fin n → ℕ)) R :=
  OrbitEvaluationDescent.descendedEval
    (RootedIncidence.exactAssignmentMap (hn := hn) (rho := rho) currentType)
    (RootedIncidence.exactAssignmentMap_surjective (hn := hn) (rho := rho) currentType)
    (fun I : RootedIncidence hn rho => M.incidenceEval currentType I)

@[simp]
theorem descendedEval_exactAssignmentMap (currentType : C → A)
    (M : InvariantScalarPolynomialRealization (R := R) (S := S) (V := V) currentType)
    (I : RootedIncidence hn rho) :
    M.descendedEval (hn := hn) (rho := rho) currentType
        (RootedIncidence.exactAssignmentMap currentType I) =
      M.incidenceEval currentType I := by
  apply OrbitEvaluationDescent.descendedEval_theta
  exact M.incidenceEval_isFiberConstant currentType

end InvariantScalarPolynomialRealization

end ModelInstantiation

end Incidence

end

end VOA.P3FunctionalModel
