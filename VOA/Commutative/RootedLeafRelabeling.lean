/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Finite.Card
import VOA.Commutative.RootedIncidence

/-!
# Relabeling the non-root leaves of rooted matchings

The canonical same-slot root equivalence between two incidence lifts preserves the number of
additional `S`-leaves at each root.  This file turns that numerical statement into a global
equivalence between all non-root `S`-labels, assembled from equivalences of the individual leaf
fibers.  The resulting equivalence intertwines the two leaf-center maps.

This is one step short of a permutation of every source label: the retained `S`-roots and the
current labels still have to be transported using the root-type assignment.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v

variable {C : Type u} {S : Type v}

/-- The non-root `S`-labels of a raw rooted matching. -/
abbrev NonRootS (m : RawRootedMatching C S) :=
  {s : S // ¬m.IsRoot (.inr s)}

instance [Finite S] (m : RawRootedMatching C S) : Finite (NonRootS m) :=
  Finite.of_injective (fun s : NonRootS m => s.1) Subtype.val_injective

/-- The root at the center of a non-root `S`-leaf. -/
def leafCenter (m : RawRootedMatching C S) (s : NonRootS m) : MatchingRoots m :=
  ⟨m.center (.inr s.1), m.center_isRoot (.inr s.1)⟩

/-- A fiber of the leaf-center map is exactly the set of additional `S`-leaves of its root. -/
private def leafCenterFiberEquiv (m : RawRootedMatching C S) (r : MatchingRoots m) :
    {s : NonRootS m // leafCenter m s = r} ≃ m.additionalSLeaves r.1 where
  toFun s := by
    refine ⟨s.1.1, ?_, ?_⟩
    · exact congrArg Subtype.val s.2
    · intro hsr
      apply s.1.2
      rw [hsr]
      exact r.2
  invFun s := by
    refine ⟨⟨s.1, ?_⟩, ?_⟩
    · intro hsroot
      exact s.2.2 (hsroot.symm.trans s.2.1)
    · apply Subtype.ext
      exact s.2.1
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

private theorem card_leafCenterFiber [Finite S] (m : RawRootedMatching C S)
    (r : MatchingRoots m) :
    Nat.card {s : NonRootS m // leafCenter m s = r} = m.additionalSLeafCount r.1 := by
  exact Nat.card_congr (leafCenterFiberEquiv m r)

namespace RootedIncidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}

/-- View the target leaf-center map in the source root set via the same-slot root equivalence. -/
private def transportedLeafCenter (I J : RootedIncidence hn rho)
    (s : NonRootS J.matching.1.1) : MatchingRoots I.matching.1.1 :=
  (I.rootEquiv J).symm (leafCenter J.matching.1.1 s)

private def transportedLeafFiberEquiv (I J : RootedIncidence hn rho)
    (r : MatchingRoots I.matching.1.1) :
    {s : NonRootS J.matching.1.1 // transportedLeafCenter I J s = r} ≃
      {s : NonRootS J.matching.1.1 // leafCenter J.matching.1.1 s = I.rootEquiv J r} :=
  Equiv.subtypeEquivRight fun s => by
    change (I.rootEquiv J).symm (leafCenter J.matching.1.1 s) = r ↔
      leafCenter J.matching.1.1 s = I.rootEquiv J r
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp

private theorem card_transportedLeafFiber (I J : RootedIncidence hn rho)
    (r : MatchingRoots I.matching.1.1) :
    Nat.card {s : NonRootS J.matching.1.1 // transportedLeafCenter I J s = r} =
      J.matching.1.1.additionalSLeafCount (I.rootEquiv J r).1 := by
  calc
    Nat.card {s : NonRootS J.matching.1.1 // transportedLeafCenter I J s = r} =
        Nat.card {s : NonRootS J.matching.1.1 //
          leafCenter J.matching.1.1 s = I.rootEquiv J r} :=
      Nat.card_congr (transportedLeafFiberEquiv I J r)
    _ = J.matching.1.1.additionalSLeafCount (I.rootEquiv J r).1 :=
      card_leafCenterFiber J.matching.1.1 (I.rootEquiv J r)

private def leafFiberEquiv (I J : RootedIncidence hn rho)
    (r : MatchingRoots I.matching.1.1) :
    {s : NonRootS I.matching.1.1 // leafCenter I.matching.1.1 s = r} ≃
      {s : NonRootS J.matching.1.1 // transportedLeafCenter I J s = r} := by
  apply Classical.choice
  apply Finite.card_eq.mp
  rw [card_leafCenterFiber, card_transportedLeafFiber]
  exact congrArg Fin.val (I.rootEquiv_preserves_color J r).symm

/-- The blockwise choices assemble to one equivalence between all non-root `S`-leaves. -/
def leafEquiv (I J : RootedIncidence hn rho) :
    NonRootS I.matching.1.1 ≃ NonRootS J.matching.1.1 :=
  Equiv.ofFiberEquiv (leafFiberEquiv I J)

/-- The assembled leaf equivalence sends a leaf centered at `r` to a leaf centered at the
same-slot target root. -/
theorem leafCenter_leafEquiv (I J : RootedIncidence hn rho)
    (s : NonRootS I.matching.1.1) :
    leafCenter J.matching.1.1 (I.leafEquiv J s) =
      I.rootEquiv J (leafCenter I.matching.1.1 s) := by
  have h := Equiv.ofFiberEquiv_map (leafFiberEquiv I J) s
  change (I.rootEquiv J).symm (leafCenter J.matching.1.1 (I.leafEquiv J s)) =
    leafCenter I.matching.1.1 s at h
  exact (I.rootEquiv J).symm_apply_eq.mp h

end RootedIncidence

end

end VOA.RootedMatching
