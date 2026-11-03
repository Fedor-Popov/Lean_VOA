/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.OrbitSectionAssembly

/-!
# Lift-independent evaluation and orbit assembly

Suppose `theta : I → A` sends a type of labelled lifts to assignment labels.  A family indexed by
`I` descends to `A` exactly when it is constant on the fibers of `theta`.  This file constructs the
descended family from a surjectivity proof and shows that equivariance survives descent.  The
resulting family can be fed directly to `OrbitSectionAssembly.assembledEval`.

The final section isolates one reusable way to prove fiber constancy.  If every fiber is a source
group orbit, an equivariant evaluation family becomes fiber-constant after restriction to source
invariants, provided the source group acts trivially on the evaluation target.

This is the generic assembly layer only.  In particular, it does not assert that a concrete
restricted-dual or literal-evaluation model satisfies the covariance hypotheses.
-/

namespace VOA.OrbitEvaluationDescent

noncomputable section

universe u v w x y z

/-- A function on labelled lifts is constant on the fibers of the assignment map. -/
def IsFiberConstant {I : Type u} {A : Type v} {X : Type w}
    (theta : I → A) (f : I → X) : Prop :=
  ∀ i j, theta i = theta j → f i = f j

/-- A noncanonical lift of an assignment along a surjective assignment map. -/
def chosenLift {I : Type u} {A : Type v} (theta : I → A)
    (hsurj : Function.Surjective theta) (a : A) : I :=
  Classical.choose (hsurj a)

@[simp]
theorem theta_chosenLift {I : Type u} {A : Type v} (theta : I → A)
    (hsurj : Function.Surjective theta) (a : A) :
    theta (chosenLift theta hsurj a) = a :=
  Classical.choose_spec (hsurj a)

/-- Descend a fiber-constant value function by evaluating at a chosen lift. -/
def descendedValue {I : Type u} {A : Type v} {X : Type w}
    (theta : I → A) (hsurj : Function.Surjective theta) (f : I → X) : A → X :=
  fun a => f (chosenLift theta hsurj a)

/-- A descended value agrees with the original value on every lift. -/
theorem descendedValue_theta {I : Type u} {A : Type v} {X : Type w}
    (theta : I → A) (hsurj : Function.Surjective theta) (f : I → X)
    (hfiber : IsFiberConstant theta f) (i : I) :
    descendedValue theta hsurj f (theta i) = f i := by
  exact hfiber _ _ (theta_chosenLift theta hsurj (theta i))

/-- Descent is independent of the chosen construction: it is the unique function whose pullback
along `theta` is `f`. -/
theorem descendedValue_unique {I : Type u} {A : Type v} {X : Type w}
    (theta : I → A) (hsurj : Function.Surjective theta) (f : I → X)
    (hfiber : IsFiberConstant theta f) {g : A → X}
    (hg : ∀ i, g (theta i) = f i) :
    g = descendedValue theta hsurj f := by
  funext a
  rw [← theta_chosenLift theta hsurj a, hg,
    descendedValue_theta theta hsurj f hfiber]

section Linear

variable {R : Type u} [Semiring R]
variable {I : Type v} {A : Type w}
variable {V : Type x} [AddCommMonoid V] [Module R V]
variable {W : Type y} [AddCommMonoid W] [Module R W]

/-- Descend a fiber-constant family of linear evaluations to assignment labels. -/
def descendedEval (theta : I → A) (hsurj : Function.Surjective theta)
    (eval : I → V →ₗ[R] W) : A → V →ₗ[R] W :=
  fun a => eval (chosenLift theta hsurj a)

@[simp]
theorem descendedEval_apply (theta : I → A) (hsurj : Function.Surjective theta)
    (eval : I → V →ₗ[R] W) (a : A) (v : V) :
    descendedEval theta hsurj eval a v = eval (chosenLift theta hsurj a) v :=
  rfl

/-- The descended linear evaluator pulls back to the original labelled evaluator. -/
theorem descendedEval_theta (theta : I → A) (hsurj : Function.Surjective theta)
    (eval : I → V →ₗ[R] W) (hfiber : IsFiberConstant theta eval) (i : I) :
    descendedEval theta hsurj eval (theta i) = eval i :=
  hfiber _ _ (theta_chosenLift theta hsurj (theta i))

section Equivariant

variable {H : Type z} [Group H]
variable [MulAction H I] [MulAction H A]
variable [MulAction H V] [DistribMulAction H W]

/-- Equivariance of the assignment map from labelled lifts. -/
def IsEquivariantAssignmentMap (theta : I → A) : Prop :=
  ∀ (h : H) i, theta (h • i) = h • theta i

/-- Fiberwise descent preserves componentwise equivariance. -/
theorem descendedEval_isEquivariantFamily
    (theta : I → A) (hsurj : Function.Surjective theta)
    (htheta : IsEquivariantAssignmentMap (H := H) theta)
    (eval : I → V →ₗ[R] W) (hfiber : IsFiberConstant theta eval)
    (heval : OrbitSectionAssembly.IsEquivariantFamily (H := H) eval) :
    OrbitSectionAssembly.IsEquivariantFamily (H := H)
      (descendedEval theta hsurj eval) := by
  intro h a v
  let i := chosenLift theta hsurj a
  have hsame : eval (chosenLift theta hsurj (h • a)) = eval (h • i) := by
    apply hfiber
    calc
      theta (chosenLift theta hsurj (h • a)) = h • a :=
        theta_chosenLift theta hsurj (h • a)
      _ = h • theta i := by
        change h • a = h • theta (chosenLift theta hsurj a)
        exact congrArg (fun b : A => h • b) (theta_chosenLift theta hsurj a).symm
      _ = theta (h • i) := (htheta h i).symm
  change eval (chosenLift theta hsurj (h • a)) (h • v) =
    h • eval (chosenLift theta hsurj a) v
  rw [hsame]
  exact heval h i v

/-- The assembled assignment-indexed evaluator is equivariant for the reindex-and-value action
defined in `OrbitSectionAssembly`. -/
theorem assembledDescendedEval_equivariant
    (theta : I → A) (hsurj : Function.Surjective theta)
    (htheta : IsEquivariantAssignmentMap (H := H) theta)
    (eval : I → V →ₗ[R] W) (hfiber : IsFiberConstant theta eval)
    (heval : OrbitSectionAssembly.IsEquivariantFamily (H := H) eval)
    (h : H) (v : V) :
    OrbitSectionAssembly.assembledEval (descendedEval theta hsurj eval) (h • v) =
      OrbitSectionAssembly.reindexSmul h
        (OrbitSectionAssembly.assembledEval (descendedEval theta hsurj eval) v) :=
  OrbitSectionAssembly.assembledEval_equivariant _
    (descendedEval_isEquivariantFamily theta hsurj htheta eval hfiber heval) h v

/-- The joint kernel after descent is the intersection of the assignment-indexed kernels. -/
theorem ker_assembledDescendedEval
    (theta : I → A) (hsurj : Function.Surjective theta)
    (eval : I → V →ₗ[R] W) :
    LinearMap.ker (OrbitSectionAssembly.assembledEval (descendedEval theta hsurj eval)) =
      ⨅ a : A, LinearMap.ker (descendedEval theta hsurj eval a) :=
  OrbitSectionAssembly.ker_assembledEval _

end Equivariant

end Linear

section OrbitFibers

variable {R : Type u} [Semiring R]
variable {G : Type v} [Group G]
variable {I : Type w} [MulAction G I]
variable {A : Type x}
variable {V : Type y} [AddCommMonoid V] [Module R V] [MulAction G V]
variable {W : Type z} [AddCommMonoid W] [Module R W] [DistribMulAction G W]

/-- Every equality in the target of `theta` is witnessed by a source-group translation.  Only
this direction is needed for lift independence. -/
def FibersAreOrbits (theta : I → A) : Prop :=
  ∀ i j, theta i = theta j → ∃ g : G, g • i = j

/-- Restrict an evaluation family along a linear inclusion. -/
def restrictEval {U : Type*} [AddCommMonoid U] [Module R U]
    (embedding : U →ₗ[R] V) (eval : I → V →ₗ[R] W) : I → U →ₗ[R] W :=
  fun i => (eval i).comp embedding

/-- Orbit fibers and evaluation covariance make the restricted family fiber-constant when the
included vectors are source-invariant and the source group acts trivially on the target.  These
are the exact generic hypotheses needed for lift-independent evaluation of invariant
restricted-dual functionals. -/
theorem restrictEval_isFiberConstant_of_orbits
    {U : Type*} [AddCommMonoid U] [Module R U]
    (theta : I → A) (horbit : FibersAreOrbits (G := G) theta)
    (embedding : U →ₗ[R] V) (hfixed : ∀ (g : G) u, g • embedding u = embedding u)
    (htrivial : ∀ (g : G) (w : W), g • w = w)
    (eval : I → V →ₗ[R] W)
    (heval : OrbitSectionAssembly.IsEquivariantFamily (H := G) eval) :
    IsFiberConstant theta (restrictEval embedding eval) := by
  intro i j hij
  rcases horbit i j hij with ⟨g, rfl⟩
  ext u
  change eval i (embedding u) = eval (g • i) (embedding u)
  calc
    eval i (embedding u) = g • eval i (embedding u) := (htrivial g _).symm
    _ = eval (g • i) (g • embedding u) := (heval g i (embedding u)).symm
    _ = eval (g • i) (embedding u) := by rw [hfixed]

end OrbitFibers

end

end VOA.OrbitEvaluationDescent
