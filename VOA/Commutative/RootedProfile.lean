/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Pi
import VOA.Commutative.RootedMatching

/-!
# Realized profiles of finite rooted matchings

This file packages the second finite combinatorial layer of the rooted Gordon argument.  The
profile of an admissible matching records, for every `j : Fin n`, the number of rooted blocks
having exactly `j` additional `S`-leaves.  A `RootedProfile` is *by definition* a profile actually
realized by an admissible labelled matching, and its `Component` is the corresponding fiber.

The realization condition makes every component nonempty and finite.  It does not identify a
component with a relabelling orbit; that is a later theorem, after the species-preserving action
has been defined.  Nor does this file define a dominance relation or an overflow profile.

The final section gives simultaneous evaluation into a dependent product of targets indexed by
one realized component.  Its kernel is the intersection of the individual kernels by
`LinearMap.ker_pi`.  The product target is only a kernel-packaging device; no carrier is defined
as its range here.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v w x

variable {C : Type u} {S : Type v}

/-- The rooted occupancy profile of an admissible matching.  Its `j`th entry counts roots whose
block has exactly `j` additional `S`-leaves.

For the boundary application one has `0 < n`.  The definition also makes sense for `n = 0`, but
then the empty vector does not record the roots, so results using the profile as complete
occupancy data must state positivity explicitly. -/
def profileOf [Finite C] [Finite S] {n : ℕ}
    (m : AdmissibleRootedMatching n C S) : Fin n → ℕ :=
  fun j =>
    {r : Root C S |
      m.1.IsRoot r ∧ m.1.additionalSLeafCount r = (j : ℕ)}.ncard

/-- Under the boundary hypothesis `0 < n`, admissibility puts the leaf count of every block in
the range indexed by `Fin n`. -/
theorem additionalSLeafCount_lt [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (r : Root C S) :
    m.1.additionalSLeafCount r < n := by
  exact lt_of_le_of_lt (m.2 r) (Nat.sub_one_lt (Nat.ne_of_gt hn))

/-- A rooted profile is a finite occupancy vector that is actually realized by an admissible
labelled matching.  Defining the type as this image leaves orbit classification as a visible
later obligation. -/
def RootedProfile (n : ℕ) (C : Type u) (S : Type v) [Finite C] [Finite S] :=
  Set.range (profileOf : AdmissibleRootedMatching n C S → Fin n → ℕ)

namespace RootedProfile

variable {n : ℕ} [Finite C] [Finite S]

/-- The realized profile carried by an admissible labelled matching. -/
def ofMatching (m : AdmissibleRootedMatching n C S) : RootedProfile n C S :=
  ⟨profileOf m, ⟨m, rfl⟩⟩

@[simp]
theorem coe_ofMatching (m : AdmissibleRootedMatching n C S) :
    (ofMatching m : Fin n → ℕ) = profileOf m :=
  rfl

theorem ofMatching_surjective :
    Function.Surjective (ofMatching : AdmissibleRootedMatching n C S → RootedProfile n C S) := by
  rintro ⟨rho, m, hm⟩
  exact ⟨m, Subtype.ext hm⟩

/-- There are only finitely many realized profiles, even though the ambient type of natural-valued
vectors is infinite. -/
instance : Finite (RootedProfile n C S) :=
  Finite.of_surjective ofMatching ofMatching_surjective

/-- The labelled matching component over a realized profile. -/
def Component (rho : RootedProfile n C S) :=
  {m : AdmissibleRootedMatching n C S // profileOf m = (rho : Fin n → ℕ)}

/-- Every realized profile has only finitely many labelled matching realizations. -/
instance (rho : RootedProfile n C S) : Finite (Component rho) := by
  unfold Component
  infer_instance

/-- Every realized profile has at least one labelled matching realization. -/
theorem component_nonempty (rho : RootedProfile n C S) : Nonempty (Component rho) := by
  rcases rho.2 with ⟨m, hm⟩
  exact ⟨⟨m, hm⟩⟩

instance (rho : RootedProfile n C S) : Nonempty (Component rho) :=
  component_nonempty rho

@[simp]
theorem profileOf_component (rho : RootedProfile n C S) (m : Component rho) :
    profileOf m.1 = (rho : Fin n → ℕ) :=
  m.2

section SimultaneousEvaluation

variable {R : Type w} [Semiring R]
variable {V : Type x} [AddCommMonoid V] [Module R V]
variable (rho : RootedProfile n C S)
variable {W : Component rho → Type*}
variable [∀ m, AddCommMonoid (W m)] [∀ m, Module R (W m)]

/-- Simultaneous evaluation of a source vector in every labelled matching component of one
realized profile.  The target family may depend on the component. -/
def simultaneousEval (eval : ∀ m : Component rho, V →ₗ[R] W m) :
    V →ₗ[R] (∀ m : Component rho, W m) :=
  LinearMap.pi eval

@[simp]
theorem simultaneousEval_apply (eval : ∀ m : Component rho, V →ₗ[R] W m)
    (v : V) (m : Component rho) :
    simultaneousEval rho eval v m = eval m v :=
  rfl

/-- The joint evaluator vanishes exactly on the intersection of the individual component
kernels. -/
theorem ker_simultaneousEval (eval : ∀ m : Component rho, V →ₗ[R] W m) :
    LinearMap.ker (simultaneousEval rho eval) =
      ⨅ m : Component rho, LinearMap.ker (eval m) :=
  LinearMap.ker_pi eval

end SimultaneousEvaluation

end RootedProfile

end

end VOA.RootedMatching
