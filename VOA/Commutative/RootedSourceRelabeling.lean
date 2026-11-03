/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.RootedLeafRelabeling

/-!
# Source relabelings reconstructed from rooted incidences

This file combines the same-slot root equivalence with the blockwise equivalence of non-root
`S`-leaves.  When the root-type assignments agree, it reconstructs a type-preserving permutation
of current labels and a permutation of all `S`-labels.  Their sum conjugates the two center maps.

The theorem is purely finite and labelled.  It does not identify any model-specific carrier or
evaluation map.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v w

variable {C : Type u} {S : Type v}

/-- Which summand of `C ⊕ S` contains a source label. -/
def rootSide : Root C S → Bool
  | .inl _ => false
  | .inr _ => true

private theorem rootSide_eq_of_typeOfRoot_eq {A : Type w} (currentType : C → A)
    {r r' : Root C S}
    (h : RootedIncidence.typeOfRoot currentType r =
      RootedIncidence.typeOfRoot currentType r') :
    rootSide r = rootSide r' := by
  cases r <;> cases r' <;> simp [RootedIncidence.typeOfRoot, rootSide] at h ⊢

/-- Current labels are canonically the roots lying in the left summand. -/
private def currentRootEquiv (m : RawRootedMatching C S) :
    C ≃ {r : MatchingRoots m // rootSide r.1 = false} where
  toFun c := ⟨⟨.inl c, m.current_isRoot c⟩, rfl⟩
  invFun r := by
    rcases r with ⟨⟨r, hr⟩, hside⟩
    cases r with
    | inl c => exact c
    | inr s => simp [rootSide] at hside
  left_inv _ := rfl
  right_inv r := by
    rcases r with ⟨⟨r, hr⟩, hside⟩
    cases r with
    | inl c => rfl
    | inr s => simp [rootSide] at hside

/-- Retained `S`-roots are canonically the roots lying in the right summand. -/
private def sRootEquiv (m : RawRootedMatching C S) :
    {s : S // m.IsRoot (.inr s)} ≃
      {r : MatchingRoots m // rootSide r.1 = true} where
  toFun s := ⟨⟨.inr s.1, s.2⟩, rfl⟩
  invFun r := by
    rcases r with ⟨⟨r, hr⟩, hside⟩
    cases r with
    | inl c => simp [rootSide] at hside
    | inr s => exact ⟨s, hr⟩
  left_inv _ := rfl
  right_inv r := by
    rcases r with ⟨⟨r, hr⟩, hside⟩
    cases r with
    | inl c => simp [rootSide] at hside
    | inr s => rfl

namespace RootedIncidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}
variable {A : Type w}

/-- Agreement of type assignments forces the same-slot root equivalence to preserve the two
source summands. -/
theorem rootEquiv_preserves_side (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (r : MatchingRoots I.matching.1.1) :
    rootSide (I.rootEquiv J r).1 = rootSide r.1 :=
  rootSide_eq_of_typeOfRoot_eq currentType
    ((I.typeAssignment_eq_iff_rootEquiv_preserves_type J currentType).mp hassign r)

private def rootSideEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) (b : Bool) :
    {r : MatchingRoots I.matching.1.1 // rootSide r.1 = b} ≃
      {r : MatchingRoots J.matching.1.1 // rootSide r.1 = b} :=
  (I.rootEquiv J).subtypeEquiv fun r => by
    rw [I.rootEquiv_preserves_side J currentType hassign r]

/-- The induced permutation of current labels. -/
def currentEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) :
    Equiv.Perm C :=
  (currentRootEquiv I.matching.1.1).trans
    ((rootSideEquiv I J currentType hassign false).trans
      (currentRootEquiv J.matching.1.1).symm)

/-- The induced equivalence of retained `S`-roots. -/
def retainedSRootEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) :
    {s : S // I.matching.1.1.IsRoot (.inr s)} ≃
      {s : S // J.matching.1.1.IsRoot (.inr s)} :=
  (sRootEquiv I.matching.1.1).trans
    ((rootSideEquiv I J currentType hassign true).trans
      (sRootEquiv J.matching.1.1).symm)

/-- Combine the retained-root equivalence and the previously constructed non-root-leaf
equivalence into a permutation of every `S`-label. -/
def sourceSEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) :
    Equiv.Perm S := by
  classical
  exact Equiv.subtypeCongr (I.retainedSRootEquiv J currentType hassign) (I.leafEquiv J)

/-- The reconstructed relabeling of the complete source label set. -/
def sourceEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) :
    Equiv.Perm (Root C S) :=
  Equiv.sumCongr (I.currentEquiv J currentType hassign)
    (I.sourceSEquiv J currentType hassign)

private theorem rootEquiv_current (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) (c : C) :
    (I.rootEquiv J ⟨.inl c, I.matching.1.1.current_isRoot c⟩).1 =
      .inl (I.currentEquiv J currentType hassign c) := by
  generalize hr : I.rootEquiv J
    ⟨.inl c, I.matching.1.1.current_isRoot c⟩ = r
  rcases r with ⟨r, hroot⟩
  cases r with
  | inl d =>
      simp [currentEquiv, rootSideEquiv, currentRootEquiv, hr]
  | inr s =>
      have hside := I.rootEquiv_preserves_side J currentType hassign
        ⟨.inl c, I.matching.1.1.current_isRoot c⟩
      simp [rootSide, hr] at hside

private theorem rootEquiv_retainedS (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (s : {s : S // I.matching.1.1.IsRoot (.inr s)}) :
    (I.rootEquiv J ⟨.inr s.1, s.2⟩).1 =
      .inr (I.retainedSRootEquiv J currentType hassign s).1 := by
  generalize hr : I.rootEquiv J ⟨.inr s.1, s.2⟩ = r
  rcases r with ⟨r, hroot⟩
  cases r with
  | inl c =>
      have hside := I.rootEquiv_preserves_side J currentType hassign ⟨.inr s.1, s.2⟩
      simp [rootSide, hr] at hside
  | inr t =>
      simp [retainedSRootEquiv, rootSideEquiv, sRootEquiv, hr]

/-- The reconstructed current permutation preserves the supplied current species. -/
theorem currentType_currentEquiv (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType) (c : C) :
    currentType (I.currentEquiv J currentType hassign c) = currentType c := by
  have htype :=
    (I.typeAssignment_eq_iff_rootEquiv_preserves_type J currentType).mp hassign
      ⟨.inl c, I.matching.1.1.current_isRoot c⟩
  rw [rootEquiv_current I J currentType hassign c] at htype
  exact Sum.inl_injective htype

/-- On a retained `S`-root, the global `S` permutation is the retained-root equivalence. -/
theorem sourceSEquiv_of_isRoot (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (s : S) (hs : I.matching.1.1.IsRoot (.inr s)) :
    I.sourceSEquiv J currentType hassign s =
      (I.retainedSRootEquiv J currentType hassign ⟨s, hs⟩).1 := by
  classical
  simp [sourceSEquiv, Equiv.subtypeCongr, Equiv.sumCompl, hs]

/-- On a non-root `S`-leaf, the global `S` permutation is the blockwise leaf equivalence. -/
theorem sourceSEquiv_of_not_isRoot (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (s : S) (hs : ¬I.matching.1.1.IsRoot (.inr s)) :
    I.sourceSEquiv J currentType hassign s = (I.leafEquiv J ⟨s, hs⟩).1 := by
  classical
  simp [sourceSEquiv, Equiv.subtypeCongr, Equiv.sumCompl, hs]

/-- On every source root, the reconstructed source permutation agrees with the canonical
same-slot root equivalence. -/
theorem sourceEquiv_root (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (r : MatchingRoots I.matching.1.1) :
    I.sourceEquiv J currentType hassign r.1 = (I.rootEquiv J r).1 := by
  rcases r with ⟨r, hr⟩
  cases r with
  | inl c =>
      change Sum.inl (I.currentEquiv J currentType hassign c) =
        (I.rootEquiv J ⟨.inl c, hr⟩).1
      exact (rootEquiv_current I J currentType hassign c).symm
  | inr s =>
      change Sum.inr (I.sourceSEquiv J currentType hassign s) =
        (I.rootEquiv J ⟨.inr s, hr⟩).1
      rw [I.sourceSEquiv_of_isRoot J currentType hassign s hr]
      exact (rootEquiv_retainedS I J currentType hassign ⟨s, hr⟩).symm

/-- On a non-root leaf, the source permutation agrees with the global leaf equivalence. -/
theorem sourceEquiv_nonRootS (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (s : S) (hs : ¬I.matching.1.1.IsRoot (.inr s)) :
    I.sourceEquiv J currentType hassign (.inr s) =
      .inr (I.leafEquiv J ⟨s, hs⟩).1 := by
  change Sum.inr (I.sourceSEquiv J currentType hassign s) = _
  rw [I.sourceSEquiv_of_not_isRoot J currentType hassign s hs]

/-- The reconstructed source relabeling conjugates the two center maps. -/
theorem sourceEquiv_center (I J : RootedIncidence hn rho) (currentType : C → A)
    (hassign : I.typeAssignment currentType = J.typeAssignment currentType)
    (x : Root C S) :
    I.sourceEquiv J currentType hassign (I.matching.1.1.center x) =
      J.matching.1.1.center (I.sourceEquiv J currentType hassign x) := by
  cases x with
  | inl c =>
      rw [I.matching.1.1.center_current c]
      change Sum.inl (I.currentEquiv J currentType hassign c) =
        J.matching.1.1.center (.inl (I.currentEquiv J currentType hassign c))
      exact (J.matching.1.1.center_current (I.currentEquiv J currentType hassign c)).symm
  | inr s =>
      by_cases hs : I.matching.1.1.IsRoot (.inr s)
      · let r : MatchingRoots I.matching.1.1 := ⟨.inr s, hs⟩
        have hsource := I.sourceEquiv_root J currentType hassign r
        calc
          I.sourceEquiv J currentType hassign (I.matching.1.1.center (.inr s)) =
              I.sourceEquiv J currentType hassign (.inr s) := congrArg _ hs
          _ = (I.rootEquiv J r).1 := hsource
          _ = J.matching.1.1.center (I.rootEquiv J r).1 :=
            (I.rootEquiv J r).2.symm
          _ = J.matching.1.1.center
              (I.sourceEquiv J currentType hassign (.inr s)) := congrArg _ hsource.symm
      · let sl : NonRootS I.matching.1.1 := ⟨s, hs⟩
        have hleaf := I.sourceEquiv_nonRootS J currentType hassign s hs
        have hcenter := I.leafCenter_leafEquiv J sl
        calc
          I.sourceEquiv J currentType hassign (I.matching.1.1.center (.inr s)) =
              (I.rootEquiv J (leafCenter I.matching.1.1 sl)).1 :=
            I.sourceEquiv_root J currentType hassign (leafCenter I.matching.1.1 sl)
          _ = (leafCenter J.matching.1.1 (I.leafEquiv J sl)).1 :=
            congrArg Subtype.val hcenter.symm
          _ = J.matching.1.1.center (.inr (I.leafEquiv J sl).1) := rfl
          _ = J.matching.1.1.center
              (I.sourceEquiv J currentType hassign (.inr s)) := congrArg _ hleaf.symm

/-- Equal typed color tables produce a species-preserving relabeling of the complete labelled
source which conjugates the two center maps.  This is the reconstruction direction of the finite
orbit theorem; it does not mention any model-specific carrier. -/
theorem exists_sourceRelabeling_of_typedColorTable_eq
    (I J : RootedIncidence hn rho) (currentType : C → A)
    (htable : I.typedColorTable currentType = J.typedColorTable currentType) :
    ∃ (eC : Equiv.Perm C) (eS : Equiv.Perm S),
      (∀ c, currentType (eC c) = currentType c) ∧
      ∀ x : Root C S,
        (Equiv.sumCongr eC eS) (I.matching.1.1.center x) =
          J.matching.1.1.center ((Equiv.sumCongr eC eS) x) := by
  rcases I.exists_slotRelabeling_typeAssignment_eq J currentType htable with
    ⟨sigma, hassign⟩
  let I' := I.relabelSlots sigma
  refine ⟨I'.currentEquiv J currentType hassign,
    I'.sourceSEquiv J currentType hassign, ?_, ?_⟩
  · exact I'.currentType_currentEquiv J currentType hassign
  · intro x
    exact I'.sourceEquiv_center J currentType hassign x

end RootedIncidence

end

end VOA.RootedMatching
