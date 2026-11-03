/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Finite.Card
import VOA.Commutative.RootedTypedProfile

/-!
# Incidence lifts of rooted profiles

A coarse rooted profile remembers how many block roots have each color, but not which root
occupies which copy of that color.  This file introduces an explicit finite set of colored slots
and packages the missing incidence datum as a color-preserving equivalence from the roots of a
matching to those slots.

An incidence lift also determines a root-type assignment on the slots.  The type of a current
root is supplied by an arbitrary map `C → A`; an `S`-root has a separate distinguished type.  In
the affine application, `A` can later encode the three current species.  No model-specific orbit
or carrier theorem is asserted here.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v w x y

variable {C : Type u} {S : Type v}

/-- The finite type of roots of a raw rooted matching. -/
abbrev MatchingRoots (m : RawRootedMatching C S) :=
  {r : Root C S // m.IsRoot r}

instance [Finite C] [Finite S] (m : RawRootedMatching C S) : Finite (MatchingRoots m) := by
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite S
  letI : Fintype (Root C S) := inferInstance
  exact Finite.of_injective (fun r : MatchingRoots m => r.1) Subtype.val_injective

/-- A profile with `rho j` roots of color `j` has one slot for every pair consisting of a color
and an index within that color. -/
def ColoredSlots {n : ℕ} (rho : Fin n → ℕ) :=
  Σ j : Fin n, Fin (rho j)

instance {n : ℕ} (rho : Fin n → ℕ) : Finite (ColoredSlots rho) := by
  unfold ColoredSlots
  infer_instance

private def fiberEquivSlot {α : Type x} {ι : Type y} [Finite α]
    (f : α → ι) (g : ι → ℕ)
    (hcard : ∀ i, Nat.card {a : α // f a = i} = g i) (i : ι) :
    {a : α // f a = i} ≃ Fin (g i) :=
  Classical.choice (Finite.card_eq.mp (by simpa using hcard i))

/-- A finite set whose color fibers have prescribed cardinalities can be enumerated by the
corresponding colored slots.  The equivalence is deliberately noncanonical within each color. -/
private def finiteColorEquiv {α : Type x} {ι : Type y} [Finite α]
    (f : α → ι) (g : ι → ℕ)
    (hcard : ∀ i, Nat.card {a : α // f a = i} = g i) :
    α ≃ Σ i : ι, Fin (g i) :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight fun i => fiberEquivSlot f g hcard i)

@[simp]
private theorem finiteColorEquiv_color {α : Type x} {ι : Type y} [Finite α]
    (f : α → ι) (g : ι → ℕ)
    (hcard : ∀ i, Nat.card {a : α // f a = i} = g i) (a : α) :
    (finiteColorEquiv f g hcard a).1 = f a :=
  rfl

/-- The color of a root, defined under the boundary assumption that the number `n` of allowed
colors is positive. -/
def rootColor [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (r : MatchingRoots m.1) : Fin n :=
  ⟨m.1.additionalSLeafCount r.1, additionalSLeafCount_lt hn m r.1⟩

private def rootColorFiberEquiv [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (j : Fin n) :
    {r : MatchingRoots m.1 // rootColor hn m r = j} ≃
      {r : Root C S // m.1.IsRoot r ∧ m.1.additionalSLeafCount r = (j : ℕ)} where
  toFun r := ⟨r.1.1, r.1.2, congrArg Fin.val r.2⟩
  invFun r := ⟨⟨r.1, r.2.1⟩, Fin.ext r.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An incidence lift of a coarse component chooses an enumeration of its roots by colored
slots.  The enumeration is required to preserve the additional-leaf color. -/
structure RootedIncidence [Finite C] [Finite S] {n : ℕ} (hn : 0 < n)
    (rho : RootedProfile n C S) where
  matching : RootedProfile.Component rho
  rootToSlot : MatchingRoots matching.1.1 ≃ ColoredSlots (rho : Fin n → ℕ)
  color_preserving : ∀ r, (rootToSlot r).1 = rootColor hn matching.1 r

namespace RootedIncidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}

private theorem card_rootColorFiber (m : RootedProfile.Component rho) (j : Fin n) :
    Nat.card {r : MatchingRoots m.1.1 // rootColor hn m.1 r = j} = (rho : Fin n → ℕ) j := by
  calc
    Nat.card {r : MatchingRoots m.1.1 // rootColor hn m.1 r = j} =
        Nat.card {r : Root C S // m.1.1.IsRoot r ∧
          m.1.1.additionalSLeafCount r = (j : ℕ)} :=
      Nat.card_congr (rootColorFiberEquiv hn m.1 j)
    _ = profileOf m.1 j := by rfl
    _ = (rho : Fin n → ℕ) j := congrFun m.2 j

/-- Every matching in a realized coarse-profile component admits at least one incidence lift.
Only the enumeration inside each color class is chosen noncanonically. -/
def ofComponent (m : RootedProfile.Component rho) : RootedIncidence hn rho where
  matching := m
  rootToSlot := finiteColorEquiv (rootColor hn m.1) (rho : Fin n → ℕ)
    (card_rootColorFiber m)
  color_preserving r := finiteColorEquiv_color (rootColor hn m.1)
    (rho : Fin n → ℕ) (card_rootColorFiber m) r

/-- In particular, every realized coarse profile has an incidence lift. -/
instance : Nonempty (RootedIncidence hn rho) := by
  exact ⟨ofComponent (Classical.choice (RootedProfile.component_nonempty rho))⟩

/-- A slot relabeling permutes the copies within each color and never mixes colors. -/
abbrev SlotRelabeling :=
  ∀ j : Fin n, Equiv.Perm (Fin ((rho : Fin n → ℕ) j))

/-- The color-preserving permutation of all colored slots induced by a slot relabeling. -/
def slotEquiv (sigma : SlotRelabeling (rho := rho)) :
    Equiv.Perm (ColoredSlots (rho : Fin n → ℕ)) :=
  Equiv.sigmaCongrRight sigma

@[simp]
theorem slotEquiv_color (sigma : SlotRelabeling (rho := rho))
    (q : ColoredSlots (rho : Fin n → ℕ)) :
    (slotEquiv sigma q).1 = q.1 :=
  rfl

/-- Postcompose the chosen root enumeration by a colorwise slot relabeling. -/
def relabelSlots (I : RootedIncidence hn rho) (sigma : SlotRelabeling (rho := rho)) :
    RootedIncidence hn rho where
  matching := I.matching
  rootToSlot := I.rootToSlot.trans (slotEquiv sigma)
  color_preserving r := by
    change (slotEquiv sigma (I.rootToSlot r)).1 = rootColor hn I.matching.1 r
    rw [slotEquiv_color, I.color_preserving]

/-- The two generic kinds of roots: a current of source type `A`, or an `S`-particle root. -/
abbrev RootType (A : Type w) := A ⊕ Unit

/-- Apply a chosen type map to current roots and give every `S`-root the distinguished right
summand type. -/
def typeOfRoot {A : Type w} (currentType : C → A) : Root C S → RootType A
  | .inl c => .inl (currentType c)
  | .inr _ => .inr ()

/-- The root-type assignment on colored slots determined by an incidence lift. -/
def typeAssignment {A : Type w} (I : RootedIncidence hn rho) (currentType : C → A) :
    ColoredSlots (rho : Fin n → ℕ) → RootType A :=
  fun q => typeOfRoot currentType (I.rootToSlot.symm q).1

/-- The typed color table counts, for every color and root type, the slots carrying that type.
This is the choice-free numerical datum underlying a root-type assignment. -/
def typedColorTable {A : Type w} (I : RootedIncidence hn rho) (currentType : C → A) :
    Fin n → RootType A → ℕ :=
  fun j a => Nat.card {q : Fin ((rho : Fin n → ℕ) j) //
    I.typeAssignment currentType ⟨j, q⟩ = a}

private def typeFiberEquiv {A : Type w} (I J : RootedIncidence hn rho)
    (currentType : C → A) (htable : I.typedColorTable currentType = J.typedColorTable currentType)
    (j : Fin n) (a : RootType A) :
    {q : Fin ((rho : Fin n → ℕ) j) // I.typeAssignment currentType ⟨j, q⟩ = a} ≃
      {q : Fin ((rho : Fin n → ℕ) j) // J.typeAssignment currentType ⟨j, q⟩ = a} :=
  Classical.choice (Finite.card_eq.mp (congrFun (congrFun htable j) a))

/-- Equal typed color tables determine, noncanonically, a permutation inside each color which
maps the first assignment to the second. -/
private def alignmentAtColor {A : Type w} (I J : RootedIncidence hn rho)
    (currentType : C → A) (htable : I.typedColorTable currentType = J.typedColorTable currentType)
    (j : Fin n) : Equiv.Perm (Fin ((rho : Fin n → ℕ) j)) :=
  Equiv.ofFiberEquiv (typeFiberEquiv I J currentType htable j)

private theorem alignmentAtColor_map {A : Type w} (I J : RootedIncidence hn rho)
    (currentType : C → A) (htable : I.typedColorTable currentType = J.typedColorTable currentType)
    (j : Fin n) (q : Fin ((rho : Fin n → ℕ) j)) :
    J.typeAssignment currentType ⟨j, alignmentAtColor I J currentType htable j q⟩ =
      I.typeAssignment currentType ⟨j, q⟩ :=
  Equiv.ofFiberEquiv_map (typeFiberEquiv I J currentType htable j) q

/-- Relabeling the slots transports the type assignment contragrediently. -/
theorem typeAssignment_relabelSlots {A : Type w} (I : RootedIncidence hn rho)
    (sigma : SlotRelabeling (rho := rho)) (currentType : C → A)
    (q : ColoredSlots (rho : Fin n → ℕ)) :
    (I.relabelSlots sigma).typeAssignment currentType q =
      I.typeAssignment currentType ((slotEquiv sigma).symm q) :=
  rfl

/-- Equality of the typed color tables is sufficient to align the complete type assignments by
a colorwise slot relabeling.  Thus the table loses only the deliberately quotientable ordering
of the copies within each color. -/
theorem exists_slotRelabeling_typeAssignment_eq {A : Type w}
    (I J : RootedIncidence hn rho) (currentType : C → A)
    (htable : I.typedColorTable currentType = J.typedColorTable currentType) :
    ∃ sigma : SlotRelabeling (rho := rho),
      (I.relabelSlots sigma).typeAssignment currentType = J.typeAssignment currentType := by
  let sigma : SlotRelabeling (rho := rho) :=
    fun j => alignmentAtColor I J currentType htable j
  refine ⟨sigma, ?_⟩
  funext q
  rcases q with ⟨j, q⟩
  rw [typeAssignment_relabelSlots]
  change I.typeAssignment currentType ⟨j, (sigma j).symm q⟩ =
    J.typeAssignment currentType ⟨j, q⟩
  have hmap := alignmentAtColor_map I J currentType htable j ((sigma j).symm q)
  simpa [sigma] using hmap.symm

@[simp]
theorem typeAssignment_rootToSlot {A : Type w} (I : RootedIncidence hn rho)
    (currentType : C → A) (r : MatchingRoots I.matching.1.1) :
    I.typeAssignment currentType (I.rootToSlot r) = typeOfRoot currentType r.1 := by
  simp [typeAssignment]

/-- Two incidence lifts over the same coarse profile carry a canonical root equivalence: identify
roots which occupy the same colored slot. -/
def rootEquiv (I J : RootedIncidence hn rho) :
    MatchingRoots I.matching.1.1 ≃ MatchingRoots J.matching.1.1 :=
  I.rootToSlot.trans J.rootToSlot.symm

@[simp]
theorem rootToSlot_rootEquiv (I J : RootedIncidence hn rho)
    (r : MatchingRoots I.matching.1.1) :
    J.rootToSlot (I.rootEquiv J r) = I.rootToSlot r := by
  simp [rootEquiv]

/-- The same-slot root equivalence automatically preserves the occupancy color. -/
theorem rootEquiv_preserves_color (I J : RootedIncidence hn rho)
    (r : MatchingRoots I.matching.1.1) :
    rootColor hn J.matching.1 (I.rootEquiv J r) = rootColor hn I.matching.1 r := by
  rw [← J.color_preserving (I.rootEquiv J r), rootToSlot_rootEquiv, I.color_preserving]

/-- Equality of slot assignments is exactly preservation of root types by the canonical
same-slot equivalence.  This is the first finite reconstruction statement: after choosing the
colored-slot incidences, no further root-type datum is hidden in the two matchings. -/
theorem typeAssignment_eq_iff_rootEquiv_preserves_type {A : Type w}
    (I J : RootedIncidence hn rho) (currentType : C → A) :
    I.typeAssignment currentType = J.typeAssignment currentType ↔
      ∀ r : MatchingRoots I.matching.1.1,
        typeOfRoot currentType (I.rootEquiv J r).1 = typeOfRoot currentType r.1 := by
  constructor
  · intro h r
    have hr := congrFun h (I.rootToSlot r)
    simpa using hr.symm
  · intro h
    funext q
    have hq := h (I.rootToSlot.symm q)
    have heq : I.rootEquiv J (I.rootToSlot.symm q) = J.rootToSlot.symm q := by
      apply J.rootToSlot.injective
      simp
    rw [heq] at hq
    exact hq.symm

end RootedIncidence

end

end VOA.RootedMatching
