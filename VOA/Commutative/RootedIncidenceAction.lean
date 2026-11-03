/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.OrbitEvaluationDescent
import VOA.Commutative.RootedIncidenceOrbit

/-!
# Source and slot actions on rooted incidences

The source relabeling group is the product of the current permutations preserving a supplied
species map and all permutations of the `S`-labels.  It acts on rooted incidences by conjugating
the center map and transporting the root-to-slot equivalence.  This action fixes the exact
root-type assignment on the slots.

Colorwise slot relabelings are a separate group.  Their orbits on exact assignments are the typed
color tables.  Keeping these two actions separate prevents the false claim that a typed-table
fiber is already one source-relabeling orbit.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v w

variable {C : Type u} {S : Type v} {A : Type w}

/-- Current permutations which preserve the chosen current species. -/
def currentSpeciesPermSubgroup (currentType : C → A) : Subgroup (Equiv.Perm C) where
  carrier := {e | ∀ c, currentType (e c) = currentType c}
  one_mem' c := rfl
  mul_mem' {e f} he hf c := (he (f c)).trans (hf c)
  inv_mem' {e} he c := by
    have h := he (e.symm c)
    simpa using h.symm

/-- Species-preserving source relabelings: a species-preserving current permutation and an
arbitrary permutation of the `S` labels. -/
abbrev SourceRelabeling (currentType : C → A) :=
  currentSpeciesPermSubgroup currentType × Equiv.Perm S

/-- The induced permutation of the disjoint source label set. -/
def SourceRelabeling.sumEquiv (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) : Equiv.Perm (Root C S) :=
  sumRelabeling g.1.1 g.2

@[simp]
theorem SourceRelabeling.sumEquiv_inl (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (c : C) :
    g.sumEquiv currentType (.inl c) = .inl (g.1.1 c) :=
  rfl

@[simp]
theorem SourceRelabeling.sumEquiv_inr (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (s : S) :
    g.sumEquiv currentType (.inr s) = .inr (g.2 s) :=
  rfl

@[simp]
theorem SourceRelabeling.typeOfRoot_sumEquiv (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (x : Root C S) :
    RootedIncidence.typeOfRoot currentType (g.sumEquiv currentType x) =
      RootedIncidence.typeOfRoot currentType x := by
  cases x with
  | inl c =>
      change Sum.inl (currentType (g.1.1 c)) = Sum.inl (currentType c)
      rw [g.1.2 c]
  | inr s => rfl

@[simp]
theorem SourceRelabeling.sumEquiv_one (currentType : C → A) :
    (1 : SourceRelabeling (S := S) currentType).sumEquiv currentType = 1 := by
  ext x
  cases x <;> rfl

@[simp]
theorem SourceRelabeling.sumEquiv_mul (currentType : C → A)
    (g h : SourceRelabeling (S := S) currentType) :
    (g * h).sumEquiv currentType = g.sumEquiv currentType * h.sumEquiv currentType := by
  ext x
  cases x <;> rfl

/-- Conjugate the center map by a source relabeling. -/
def relabelRaw (currentType : C → A) (g : SourceRelabeling (S := S) currentType)
    (m : RawRootedMatching C S) : RawRootedMatching C S where
  center x := g.sumEquiv currentType (m.center ((g.sumEquiv currentType).symm x))
  center_current c := by
    change sumRelabeling g.1.1 g.2
      (m.center (.inl (g.1.1.symm c))) = .inl c
    rw [m.center_current]
    simp
  center_idem x := by simp [m.center_idem]

@[simp]
theorem relabelRaw_center (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S)
    (x : Root C S) :
    (relabelRaw currentType g m).center (g.sumEquiv currentType x) =
      g.sumEquiv currentType (m.center x) := by
  simp [relabelRaw]

@[simp]
theorem relabelRaw_one (currentType : C → A) (m : RawRootedMatching C S) :
    relabelRaw currentType 1 m = m := by
  ext x
  change (1 : SourceRelabeling (S := S) currentType).sumEquiv currentType
    (m.center (((1 : SourceRelabeling (S := S) currentType).sumEquiv currentType).symm x)) =
      m.center x
  rw [SourceRelabeling.sumEquiv_one]
  rfl

@[simp]
theorem relabelRaw_mul (currentType : C → A)
    (g h : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S) :
    relabelRaw currentType (g * h) m =
      relabelRaw currentType g (relabelRaw currentType h m) := by
  ext x
  change (g * h).sumEquiv currentType
      (m.center (((g * h).sumEquiv currentType).symm x)) =
    g.sumEquiv currentType
      (h.sumEquiv currentType
        (m.center ((h.sumEquiv currentType).symm ((g.sumEquiv currentType).symm x))))
  rw [show (g * h).sumEquiv currentType =
    g.sumEquiv currentType * h.sumEquiv currentType from
      SourceRelabeling.sumEquiv_mul currentType g h]
  change (g.sumEquiv currentType * h.sumEquiv currentType)
      (m.center ((g.sumEquiv currentType * h.sumEquiv currentType).symm x)) =
    (g.sumEquiv currentType * h.sumEquiv currentType)
      (m.center ((h.sumEquiv currentType).symm ((g.sumEquiv currentType).symm x)))
  apply congrArg (g.sumEquiv currentType * h.sumEquiv currentType)
  apply congrArg m.center
  apply (g.sumEquiv currentType * h.sumEquiv currentType).injective
  simp

private theorem additionalSLeafCount_eq_zero_of_not_isRoot [Finite S]
    (m : RawRootedMatching C S) (r : Root C S) (hr : ¬m.IsRoot r) :
    m.additionalSLeafCount r = 0 := by
  rw [RawRootedMatching.additionalSLeafCount, Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  apply hr
  rw [← hs.1]
  exact m.center_idem (.inr s)

/-- The root equivalence induced by a source relabeling and conjugation. -/
def relabelRootEquiv (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S) :
    MatchingRoots m ≃ MatchingRoots (relabelRaw currentType g m) :=
  rootsEquivOfSourceRelabeling m (relabelRaw currentType g m) g.1.1 g.2
    (fun x => (relabelRaw_center currentType g m x).symm)

@[simp]
theorem relabelRootEquiv_apply_val (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S)
    (r : MatchingRoots m) :
    (relabelRootEquiv currentType g m r).1 = g.sumEquiv currentType r.1 :=
  rfl

/-- Conjugation preserves the additional-leaf count at corresponding roots. -/
theorem additionalSLeafCount_relabelRootEquiv [Finite S] (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RawRootedMatching C S)
    (r : MatchingRoots m) :
    (relabelRaw currentType g m).additionalSLeafCount
        (relabelRootEquiv currentType g m r).1 = m.additionalSLeafCount r.1 :=
  additionalSLeafCount_rootsEquivOfSourceRelabeling m (relabelRaw currentType g m)
    g.1.1 g.2 (fun x => (relabelRaw_center currentType g m x).symm) r

/-- Source relabeling preserves admissibility. -/
def relabelMatching [Finite S] {n : ℕ} (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType)
    (m : AdmissibleRootedMatching n C S) : AdmissibleRootedMatching n C S where
  val := relabelRaw currentType g m.1
  property r := by
    by_cases hr : (relabelRaw currentType g m.1).IsRoot r
    · let rr : MatchingRoots (relabelRaw currentType g m.1) := ⟨r, hr⟩
      let r0 := (relabelRootEquiv currentType g m.1).symm rr
      have hcount := additionalSLeafCount_relabelRootEquiv currentType g m.1 r0
      have heroot : relabelRootEquiv currentType g m.1 r0 = rr :=
        (relabelRootEquiv currentType g m.1).apply_symm_apply rr
      rw [heroot] at hcount
      exact hcount.trans_le (m.2 r0.1)
    · rw [additionalSLeafCount_eq_zero_of_not_isRoot _ r hr]
      exact Nat.zero_le _

private def profileFiberEquiv [Finite S] {n : ℕ} (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType)
    (m : AdmissibleRootedMatching n C S) (j : Fin n) :
    {r : Root C S // m.1.IsRoot r ∧ m.1.additionalSLeafCount r = (j : ℕ)} ≃
      {r : Root C S // (relabelMatching currentType g m).1.IsRoot r ∧
        (relabelMatching currentType g m).1.additionalSLeafCount r = (j : ℕ)} :=
  (g.sumEquiv currentType).subtypeEquiv fun r => by
    constructor
    · rintro ⟨hroot, hcount⟩
      let rr : MatchingRoots m.1 := ⟨r, hroot⟩
      exact ⟨(relabelRootEquiv currentType g m.1 rr).2,
        (additionalSLeafCount_relabelRootEquiv currentType g m.1 rr).trans hcount⟩
    · rintro ⟨hroot, hcount⟩
      have hroot' : m.1.IsRoot r :=
        (isRoot_sumRelabeling_iff m.1 (relabelRaw currentType g m.1) g.1.1 g.2
          (fun x => (relabelRaw_center currentType g m.1 x).symm) r).mpr hroot
      let rr : MatchingRoots m.1 := ⟨r, hroot'⟩
      refine ⟨hroot', ?_⟩
      exact (additionalSLeafCount_relabelRootEquiv currentType g m.1 rr).symm.trans hcount

/-- The coarse profile is invariant under source relabeling. -/
theorem profileOf_relabelMatching [Finite C] [Finite S] {n : ℕ}
    (currentType : C → A) (g : SourceRelabeling (S := S) currentType)
    (m : AdmissibleRootedMatching n C S) :
    profileOf (relabelMatching currentType g m) = profileOf m := by
  funext j
  exact (Nat.card_congr (profileFiberEquiv currentType g m j)).symm

@[simp]
theorem relabelMatching_one [Finite S] {n : ℕ} (currentType : C → A)
    (m : AdmissibleRootedMatching n C S) :
    relabelMatching currentType 1 m = m := by
  apply Subtype.ext
  exact relabelRaw_one currentType m.1

@[simp]
theorem relabelMatching_mul [Finite S] {n : ℕ} (currentType : C → A)
    (g h : SourceRelabeling (S := S) currentType)
    (m : AdmissibleRootedMatching n C S) :
    relabelMatching currentType (g * h) m =
      relabelMatching currentType g (relabelMatching currentType h m) := by
  apply Subtype.ext
  exact relabelRaw_mul currentType g h m.1

/-- The strict source-group action on raw rooted matchings. -/
@[reducible]
def sourceMulActionRaw (currentType : C → A) :
    MulAction (SourceRelabeling (S := S) currentType) (RawRootedMatching C S) where
  smul := relabelRaw currentType
  one_smul := relabelRaw_one currentType
  mul_smul := relabelRaw_mul currentType

/-- The strict source-group action on admissible rooted matchings. -/
@[reducible]
def sourceMulActionMatching [Finite S] {n : ℕ} (currentType : C → A) :
    MulAction (SourceRelabeling (S := S) currentType) (AdmissibleRootedMatching n C S) where
  smul := relabelMatching currentType
  one_smul := relabelMatching_one currentType
  mul_smul := relabelMatching_mul currentType

namespace RootedIncidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}

/-- Transport a matching component by a source relabeling. -/
def relabelComponent (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (m : RootedProfile.Component rho) :
    RootedProfile.Component rho where
  val := relabelMatching currentType g m.1
  property := (profileOf_relabelMatching currentType g m.1).trans m.2

/-- Transport a rooted incidence by a source relabeling.  The slots are fixed: a new root is
first pulled back to the old matching and then sent to its old slot. -/
def relabel (currentType : C → A) (g : SourceRelabeling (S := S) currentType)
    (I : RootedIncidence hn rho) : RootedIncidence hn rho where
  matching := relabelComponent currentType g I.matching
  rootToSlot := (relabelRootEquiv currentType g I.matching.1.1).symm.trans I.rootToSlot
  color_preserving r := by
    let E := relabelRootEquiv currentType g I.matching.1.1
    let r0 := E.symm r
    change (I.rootToSlot r0).1 = rootColor hn (relabelMatching currentType g I.matching.1) r
    rw [I.color_preserving]
    apply Fin.ext
    have hcount := additionalSLeafCount_relabelRootEquiv currentType g I.matching.1.1 r0
    have heroot : E r0 = r := E.apply_symm_apply r
    rw [heroot] at hcount
    exact hcount.symm

/-- Source relabeling fixes the exact root-type assignment because it moves roots while leaving
their colored slots fixed. -/
theorem typeAssignment_relabel (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (I : RootedIncidence hn rho) :
    (I.relabel currentType g).typeAssignment currentType = I.typeAssignment currentType := by
  funext q
  change RootedIncidence.typeOfRoot currentType
      (g.sumEquiv currentType (I.rootToSlot.symm q).1) =
    RootedIncidence.typeOfRoot currentType (I.rootToSlot.symm q).1
  exact g.typeOfRoot_sumEquiv currentType (I.rootToSlot.symm q).1

/-- The graph of the source action on rooted incidences.  Besides center conjugacy it records
that the root transported by the source permutation occupies its original slot.  This
proof-relevant formulation avoids arbitrary casts between dependent root subtypes. -/
structure IsSourceTranslate (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType)
    (I J : RootedIncidence hn rho) : Prop where
  center : ∀ x : Root C S,
    g.sumEquiv currentType (I.matching.1.1.center x) =
      J.matching.1.1.center (g.sumEquiv currentType x)
  slots : ∀ r : MatchingRoots I.matching.1.1,
    J.rootToSlot
        (rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1 g.1.1 g.2 center r) =
      I.rootToSlot r

/-- The explicitly transported incidence lies on the graph of the source action. -/
theorem isSourceTranslate_relabel (currentType : C → A)
    (g : SourceRelabeling (S := S) currentType) (I : RootedIncidence hn rho) :
    IsSourceTranslate currentType g I (I.relabel currentType g) where
  center x := (relabelRaw_center currentType g I.matching.1.1 x).symm
  slots r := by
    change I.rootToSlot
      ((relabelRootEquiv currentType g I.matching.1.1).symm
        (rootsEquivOfSourceRelabeling I.matching.1.1
          (relabelRaw currentType g I.matching.1.1) g.1.1 g.2 _ r)) = I.rootToSlot r
    apply congrArg I.rootToSlot
    apply Subtype.ext
    let E0 := relabelRootEquiv currentType g I.matching.1.1
    let E1 := rootsEquivOfSourceRelabeling I.matching.1.1
      (relabelRaw currentType g I.matching.1.1) g.1.1 g.2
      (fun x => (relabelRaw_center currentType g I.matching.1.1 x).symm)
    have hE : E0 = E1 := by
      ext r
      rfl
    change (E0.symm (E1 r)).1 = r.1
    rw [hE]
    exact congrArg Subtype.val (E1.symm_apply_apply r)

/-- Every source translation preserves the exact assignment, not merely its typed table. -/
theorem typeAssignment_eq_of_isSourceTranslate (currentType : C → A)
    {g : SourceRelabeling (S := S) currentType} {I J : RootedIncidence hn rho}
    (h : IsSourceTranslate currentType g I J) :
    I.typeAssignment currentType = J.typeAssignment currentType := by
  funext q
  let r := I.rootToSlot.symm q
  let r' := rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1
    g.1.1 g.2 h.center r
  have hslot : J.rootToSlot r' = q := (h.slots r).trans (I.rootToSlot.apply_symm_apply q)
  have hr' : J.rootToSlot.symm q = r' := by
    apply J.rootToSlot.injective
    rw [hslot]
    exact J.rootToSlot.apply_symm_apply q
  change RootedIncidence.typeOfRoot currentType r.1 =
    RootedIncidence.typeOfRoot currentType (J.rootToSlot.symm q).1
  rw [hr']
  exact (g.typeOfRoot_sumEquiv currentType r.1).symm

/-- Equality of exact assignments reconstructs a source translation without any slot
relabeling. -/
theorem exists_isSourceTranslate_of_typeAssignment_eq (currentType : C → A)
    (I J : RootedIncidence hn rho)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) :
    ∃ g : SourceRelabeling (S := S) currentType,
      IsSourceTranslate currentType g I J := by
  let eC := I.currentEquiv J currentType hassign
  let eS := I.sourceSEquiv J currentType hassign
  let g : SourceRelabeling (S := S) currentType :=
    (⟨eC, I.currentType_currentEquiv J currentType hassign⟩, eS)
  have hcenter : ∀ x : Root C S,
      g.sumEquiv currentType (I.matching.1.1.center x) =
        J.matching.1.1.center (g.sumEquiv currentType x) :=
    I.sourceEquiv_center J currentType hassign
  refine ⟨g, ⟨hcenter, ?_⟩⟩
  intro r
  have hroots :
      rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1
          g.1.1 g.2 hcenter r = I.rootEquiv J r := by
    apply Subtype.ext
    exact I.sourceEquiv_root J currentType hassign r
  rw [hroots]
  exact I.rootToSlot_rootEquiv J r

/-- Two incidences lie in the same source-relabeling orbit when some species-preserving source
translation relates them. -/
def SourceOrbitRelated (currentType : C → A) (I J : RootedIncidence hn rho) : Prop :=
  ∃ g : SourceRelabeling (S := S) currentType, IsSourceTranslate currentType g I J

/-- Exact assignment fibers are precisely source-relabeling orbits.  This is the relation-valued
counterpart of `OrbitEvaluationDescent.FibersAreOrbits`; no slot relabeling occurs here. -/
theorem typeAssignment_eq_iff_sourceOrbitRelated (currentType : C → A)
    (I J : RootedIncidence hn rho) :
    I.typeAssignment currentType = J.typeAssignment currentType ↔
      SourceOrbitRelated currentType I J := by
  constructor
  · exact exists_isSourceTranslate_of_typeAssignment_eq currentType I J
  · rintro ⟨g, h⟩
    exact typeAssignment_eq_of_isSourceTranslate currentType h

/-- The type of exact assignments which are actually realized by an incidence lift. -/
def RealizedAssignments (currentType : C → A) :=
  Set.range (fun I : RootedIncidence hn rho => I.typeAssignment currentType)

/-- The canonical surjection from incidence lifts to realized exact assignments. -/
def exactAssignmentMap (currentType : C → A) (I : RootedIncidence hn rho) :
    RealizedAssignments (hn := hn) (rho := rho) currentType :=
  ⟨I.typeAssignment currentType, I, rfl⟩

/-- Every realized assignment has an incidence lift by definition. -/
theorem exactAssignmentMap_surjective (currentType : C → A) :
    Function.Surjective
      (exactAssignmentMap (hn := hn) (rho := rho) currentType) := by
  rintro ⟨assignment, I, rfl⟩
  exact ⟨I, rfl⟩

/-- Fibers of the canonical exact-assignment map are precisely the source groupoid orbits. -/
theorem exactAssignmentMap_eq_iff_sourceOrbitRelated (currentType : C → A)
    (I J : RootedIncidence hn rho) :
    exactAssignmentMap currentType I = exactAssignmentMap currentType J ↔
      SourceOrbitRelated currentType I J := by
  rw [Subtype.ext_iff]
  exact typeAssignment_eq_iff_sourceOrbitRelated currentType I J

/-- A value function invariant under every source translation is constant on exact-assignment
fibers.  This is the groupoid-form replacement for a literal use of
`OrbitEvaluationDescent.FibersAreOrbits`. -/
theorem isFiberConstant_exactAssignmentMap_of_source_invariant
    {X : Type*} (currentType : C → A) (f : RootedIncidence hn rho → X)
    (hinv : ∀ (g : SourceRelabeling (S := S) currentType) (I J : RootedIncidence hn rho),
      IsSourceTranslate currentType g I J → f I = f J) :
    OrbitEvaluationDescent.IsFiberConstant (exactAssignmentMap currentType) f := by
  intro I J hij
  have horbit : SourceOrbitRelated currentType I J :=
    (exactAssignmentMap_eq_iff_sourceOrbitRelated currentType I J).mp hij
  rcases horbit with ⟨g, hg⟩
  exact hinv g I J hg

/-- Source-orbit relatedness is an equivalence relation because it is exactly equality of the
assignment map. -/
theorem sourceOrbitRelated_equivalence (currentType : C → A) :
    Equivalence (SourceOrbitRelated (hn := hn) (rho := rho) currentType) := by
  constructor
  · intro I
    exact (typeAssignment_eq_iff_sourceOrbitRelated currentType I I).mp rfl
  · intro I J h
    apply (typeAssignment_eq_iff_sourceOrbitRelated currentType J I).mp
    exact (typeAssignment_eq_iff_sourceOrbitRelated currentType I J).mpr h |>.symm
  · intro I J K hIJ hJK
    apply (typeAssignment_eq_iff_sourceOrbitRelated currentType I K).mp
    exact ((typeAssignment_eq_iff_sourceOrbitRelated currentType I J).mpr hIJ).trans
      ((typeAssignment_eq_iff_sourceOrbitRelated currentType J K).mpr hJK)

/-- Slot relabeling leaves the typed table unchanged, although it generally changes the exact
assignment. -/
theorem typedColorTable_relabelSlots (currentType : C → A)
    (I : RootedIncidence hn rho) (sigma : SlotRelabeling (rho := rho)) :
    (I.relabelSlots sigma).typedColorTable currentType = I.typedColorTable currentType := by
  apply typedColorTable_eq_of_sourceRelabeling (I.relabelSlots sigma) I currentType 1 1
  · intro c
    rfl
  · intro x
    simp [sumRelabeling, relabelSlots]

/-- Typed-table fibers are exact-assignment orbits for the separate colorwise slot-relabeling
group.  Equivalently, typed tables classify the combined source-and-slot groupoid. -/
theorem typedColorTable_eq_iff_exists_slotRelabeling_assignment_eq
    (currentType : C → A) (I J : RootedIncidence hn rho) :
    I.typedColorTable currentType = J.typedColorTable currentType ↔
      ∃ sigma : SlotRelabeling (rho := rho),
        (I.relabelSlots sigma).typeAssignment currentType = J.typeAssignment currentType := by
  constructor
  · exact I.exists_slotRelabeling_typeAssignment_eq J currentType
  · rintro ⟨sigma, hassign⟩
    rw [← typedColorTable_relabelSlots currentType I sigma]
    unfold typedColorTable
    rw [hassign]

end RootedIncidence

end

end VOA.RootedMatching
