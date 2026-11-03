/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import Mathlib.Data.Setoid.Basic

/-!
# Finite rooted matchings

This file contains the first, purely finite combinatorial layer of the rooted Gordon argument.
A matching is encoded by an idempotent center map on the disjoint union of current roots and
`S`-particles.  Current roots are required to be fixed.  Consequently, the fibers of the center
map are the rooted blocks and each block contains at most one current root.

Admissibility is a predicate on raw matchings: a block may contain at most `n - 1` additional
`S`-leaves besides its center.  Overflow is kept as the complementary outcome, rather than being
adjoined as a profile.  No species action, orbit classification, profile order, or evaluation map
is asserted here.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v

/-- The possible block centers: either a current root or an `S`-particle root. -/
abbrev Root (C : Type u) (S : Type v) := C ⊕ S

/-- A labelled rooted matching, represented by its idempotent center map.

The fiber over a fixed point of `center` is a block.  Requiring every current root to be fixed
forces different current roots to lie in different blocks. -/
@[ext]
structure RawRootedMatching (C : Type u) (S : Type v) where
  center : Root C S → Root C S
  center_current : ∀ c : C, center (.inl c) = .inl c
  center_idem : ∀ x, center (center x) = center x

namespace RawRootedMatching

variable {C : Type u} {S : Type v}

/-- The block fiber with designated center `r`.  It is nonempty precisely when `r` is fixed. -/
def fiber (m : RawRootedMatching C S) (r : Root C S) : Set (Root C S) :=
  {x | m.center x = r}

/-- A point is a root when it is fixed by the center map. -/
def IsRoot (m : RawRootedMatching C S) (r : Root C S) : Prop :=
  m.center r = r

theorem center_isRoot (m : RawRootedMatching C S) (x : Root C S) :
    m.IsRoot (m.center x) :=
  m.center_idem x

theorem isRoot_iff_mem_range (m : RawRootedMatching C S) (r : Root C S) :
    m.IsRoot r ↔ r ∈ Set.range m.center := by
  constructor
  · exact fun hr => ⟨r, hr⟩
  · rintro ⟨x, rfl⟩
    exact m.center_isRoot x

theorem center_mem_fiber (m : RawRootedMatching C S) (x : Root C S) :
    m.center x ∈ m.fiber (m.center x) :=
  m.center_idem x

theorem self_mem_fiber_iff (m : RawRootedMatching C S) (r : Root C S) :
    r ∈ m.fiber r ↔ m.IsRoot r :=
  Iff.rfl

theorem fiber_nonempty_iff_isRoot (m : RawRootedMatching C S) (r : Root C S) :
    (m.fiber r).Nonempty ↔ m.IsRoot r := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact m.center_idem x
  · exact fun hr => ⟨r, hr⟩

theorem isRoot_center_eq (m : RawRootedMatching C S) {r x : Root C S}
    (hr : m.IsRoot r) (hx : x ∈ m.fiber r) :
    m.center x = m.center r := by
  exact hx.trans hr.symm

/-- Two labels are in the same block when they have the same center. -/
def blockSetoid (m : RawRootedMatching C S) : Setoid (Root C S) :=
  Setoid.ker m.center

theorem blockSetoid_rel_iff (m : RawRootedMatching C S) (x y : Root C S) :
    m.blockSetoid x y ↔ m.center x = m.center y :=
  Iff.rfl

theorem same_fiber_of_blockSetoid (m : RawRootedMatching C S) {x y : Root C S}
    (hxy : m.blockSetoid x y) :
    y ∈ m.fiber (m.center x) :=
  hxy.symm

/-- Every current label is the root of its own block. -/
theorem current_isRoot (m : RawRootedMatching C S) (c : C) :
    m.IsRoot (.inl c) :=
  m.center_current c

/-- A block contains at most one current root. -/
theorem current_unique_in_fiber (m : RawRootedMatching C S) {r : Root C S} {c d : C}
    (hc : (.inl c : Root C S) ∈ m.fiber r)
    (hd : (.inl d : Root C S) ∈ m.fiber r) :
    c = d := by
  change m.center (.inl c) = r at hc
  change m.center (.inl d) = r at hd
  rw [m.center_current c] at hc
  rw [m.center_current d] at hd
  exact Sum.inl_injective (hc.trans hd.symm)

/-- The `S`-labels in the block centered at `r`. -/
def sFiber (m : RawRootedMatching C S) (r : Root C S) :=
  {s : S | m.center (.inr s) = r}

/-- The `S`-leaves in a block, excluding the center itself when the center is an `S`-root. -/
def additionalSLeaves (m : RawRootedMatching C S) (r : Root C S) :=
  {s : S | m.center (.inr s) = r ∧ (.inr s : Root C S) ≠ r}

/-- The number of additional `S`-leaves in the block centered at `r`. -/
def additionalSLeafCount [Finite S] (m : RawRootedMatching C S) (r : Root C S) : ℕ :=
  (m.additionalSLeaves r).ncard

/-- Every block has at most `n - 1` additional `S`-leaves. -/
def IsAdmissible [Finite S] (n : ℕ) (m : RawRootedMatching C S) : Prop :=
  ∀ r : Root C S, m.additionalSLeafCount r ≤ n - 1

/-- Overflow is a separate outcome, witnessed by an overfull block; it is not an additional
rooted profile. -/
def IsOverflow [Finite S] (n : ℕ) (m : RawRootedMatching C S) : Prop :=
  ∃ r : Root C S, n - 1 < m.additionalSLeafCount r

theorem isOverflow_iff_not_isAdmissible [Finite S] (n : ℕ)
    (m : RawRootedMatching C S) :
    m.IsOverflow n ↔ ¬m.IsAdmissible n :=
  by
    simp only [IsOverflow, IsAdmissible, not_forall, not_le]

instance [Finite C] [Finite S] : Finite (RawRootedMatching C S) := by
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite S
  exact Finite.of_injective (fun m => m.center) (fun _ _ h => RawRootedMatching.ext h)

end RawRootedMatching

/-- The finite type of admissible labelled matchings.  Profiles will later be defined from the
realized `profileOf` image of this type, not by adjoining an overflow point. -/
def AdmissibleRootedMatching (n : ℕ) (C : Type u) (S : Type v) [Finite S] :=
  {m : RawRootedMatching C S // m.IsAdmissible n}

instance [Finite C] [Finite S] : Finite (AdmissibleRootedMatching n C S) :=
  by
    unfold AdmissibleRootedMatching
    infer_instance

end

end VOA.RootedMatching
