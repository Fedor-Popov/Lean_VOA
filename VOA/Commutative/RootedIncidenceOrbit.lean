/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.RootedSourceRelabeling

/-!
# The finite typed-table orbit theorem

This file proves the converse to source reconstruction.  A species-preserving permutation of the
current labels, together with a permutation of the `S`-labels which conjugates two center maps,
preserves the typed color table.  Combined with the reconstruction theorem, equality of typed
color tables is therefore equivalent to existence of such a source relabeling.

No quotient type, carrier, or model-specific evaluation map is introduced.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v w

variable {C : Type u} {S : Type v}

/-- The permutation of all source labels induced by independent current and `S` relabelings. -/
def sumRelabeling (eC : Equiv.Perm C) (eS : Equiv.Perm S) : Equiv.Perm (Root C S) :=
  Equiv.sumCongr eC eS

@[simp]
theorem sumRelabeling_inl (eC : Equiv.Perm C) (eS : Equiv.Perm S) (c : C) :
    sumRelabeling eC eS (.inl c) = .inl (eC c) :=
  rfl

@[simp]
theorem sumRelabeling_inr (eC : Equiv.Perm C) (eS : Equiv.Perm S) (s : S) :
    sumRelabeling eC eS (.inr s) = .inr (eS s) :=
  rfl

/-- Center conjugacy is exactly what is needed for the source relabeling to preserve root
status. -/
theorem isRoot_sumRelabeling_iff (m m' : RawRootedMatching C S)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (m.center x) = m'.center (sumRelabeling eC eS x))
    (x : Root C S) :
    m.IsRoot x ↔ m'.IsRoot (sumRelabeling eC eS x) := by
  constructor
  · intro hx
    change m'.center (sumRelabeling eC eS x) = sumRelabeling eC eS x
    rw [← hcenter, hx]
  · intro hx
    apply (sumRelabeling eC eS).injective
    rw [hcenter, hx]

/-- A center-conjugating source relabeling restricts to an equivalence of the root sets. -/
def rootsEquivOfSourceRelabeling (m m' : RawRootedMatching C S)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (m.center x) = m'.center (sumRelabeling eC eS x)) :
    MatchingRoots m ≃ MatchingRoots m' :=
  (sumRelabeling eC eS).subtypeEquiv fun x =>
    isRoot_sumRelabeling_iff m m' eC eS hcenter x

private def additionalSLeavesEquiv (m m' : RawRootedMatching C S)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (m.center x) = m'.center (sumRelabeling eC eS x))
    (r : MatchingRoots m) :
    m.additionalSLeaves r.1 ≃
      m'.additionalSLeaves (rootsEquivOfSourceRelabeling m m' eC eS hcenter r).1 :=
  eS.subtypeEquiv fun s => by
    change (m.center (.inr s) = r.1 ∧ (.inr s : Root C S) ≠ r.1) ↔
      (m'.center (.inr (eS s)) = sumRelabeling eC eS r.1 ∧
        (.inr (eS s) : Root C S) ≠ sumRelabeling eC eS r.1)
    constructor
    · rintro ⟨hc, hne⟩
      constructor
      · simpa [hc] using (hcenter (.inr s)).symm
      · intro heq
        apply hne
        apply (sumRelabeling eC eS).injective
        simpa using heq
    · rintro ⟨hc, hne⟩
      constructor
      · apply (sumRelabeling eC eS).injective
        rw [hcenter]
        exact hc
      · intro heq
        apply hne
        exact congrArg (sumRelabeling eC eS) heq

/-- The restricted root equivalence preserves the number of additional `S`-leaves. -/
theorem additionalSLeafCount_rootsEquivOfSourceRelabeling [Finite S]
    (m m' : RawRootedMatching C S) (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (m.center x) = m'.center (sumRelabeling eC eS x))
    (r : MatchingRoots m) :
    m'.additionalSLeafCount (rootsEquivOfSourceRelabeling m m' eC eS hcenter r).1 =
      m.additionalSLeafCount r.1 := by
  exact (Nat.card_congr (additionalSLeavesEquiv m m' eC eS hcenter r)).symm

namespace RootedIncidence

variable [Finite C] [Finite S] {n : ℕ} {hn : 0 < n}
variable {rho : RootedProfile n C S}
variable {A : Type w}

private theorem rootColor_rootsEquivOfSourceRelabeling
    (I J : RootedIncidence hn rho) (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (I.matching.1.1.center x) =
        J.matching.1.1.center (sumRelabeling eC eS x))
    (r : MatchingRoots I.matching.1.1) :
    rootColor hn J.matching.1
        (rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1 eC eS hcenter r) =
      rootColor hn I.matching.1 r := by
  apply Fin.ext
  exact additionalSLeafCount_rootsEquivOfSourceRelabeling
    I.matching.1.1 J.matching.1.1 eC eS hcenter r

omit [Finite C] [Finite S] in
private theorem typeOfRoot_sumRelabeling (currentType : C → A)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (htype : ∀ c, currentType (eC c) = currentType c) (x : Root C S) :
    typeOfRoot currentType (sumRelabeling eC eS x) = typeOfRoot currentType x := by
  cases x with
  | inl c =>
      change Sum.inl (currentType (eC c)) = Sum.inl (currentType c)
      rw [htype c]
  | inr s => rfl

private theorem rootColor_rootToSlot_symm (I : RootedIncidence hn rho)
    (q : ColoredSlots (rho : Fin n → ℕ)) :
    rootColor hn I.matching.1 (I.rootToSlot.symm q) = q.1 := by
  rw [← I.color_preserving]
  simp

private def fixedColorSlotEquiv (I : RootedIncidence hn rho) (currentType : C → A)
    (j : Fin n) (a : RootType A) :
    {q : Fin ((rho : Fin n → ℕ) j) // I.typeAssignment currentType ⟨j, q⟩ = a} ≃
      {q : ColoredSlots (rho : Fin n → ℕ) //
        q.1 = j ∧ I.typeAssignment currentType q = a} where
  toFun q := ⟨⟨j, q.1⟩, rfl, q.2⟩
  invFun q := by
    rcases q with ⟨⟨k, q⟩, hk, ha⟩
    cases hk
    exact ⟨q, ha⟩
  left_inv _ := rfl
  right_inv q := by
    rcases q with ⟨⟨k, q⟩, hk, ha⟩
    cases hk
    rfl

private def tableFiberRootEquiv (I : RootedIncidence hn rho) (currentType : C → A)
    (j : Fin n) (a : RootType A) :
    {q : Fin ((rho : Fin n → ℕ) j) // I.typeAssignment currentType ⟨j, q⟩ = a} ≃
      {r : MatchingRoots I.matching.1.1 //
        rootColor hn I.matching.1 r = j ∧ typeOfRoot currentType r.1 = a} :=
  (fixedColorSlotEquiv I currentType j a).trans
    (I.rootToSlot.symm.subtypeEquiv fun q => by
      simp only [typeAssignment]
      rw [rootColor_rootToSlot_symm])

private def typedRootFiberEquivOfSourceRelabeling
    (I J : RootedIncidence hn rho) (currentType : C → A)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (htype : ∀ c, currentType (eC c) = currentType c)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (I.matching.1.1.center x) =
        J.matching.1.1.center (sumRelabeling eC eS x))
    (j : Fin n) (a : RootType A) :
    {r : MatchingRoots I.matching.1.1 //
      rootColor hn I.matching.1 r = j ∧ typeOfRoot currentType r.1 = a} ≃
      {r : MatchingRoots J.matching.1.1 //
        rootColor hn J.matching.1 r = j ∧ typeOfRoot currentType r.1 = a} :=
  (rootsEquivOfSourceRelabeling I.matching.1.1 J.matching.1.1 eC eS hcenter).subtypeEquiv
    fun r => by
      rw [rootColor_rootsEquivOfSourceRelabeling I J eC eS hcenter r]
      change (rootColor hn I.matching.1 r = j ∧ typeOfRoot currentType r.1 = a) ↔
        (rootColor hn I.matching.1 r = j ∧
          typeOfRoot currentType (sumRelabeling eC eS r.1) = a)
      rw [typeOfRoot_sumRelabeling currentType eC eS htype r.1]

/-- A species-preserving, center-conjugating source relabeling preserves the typed color table. -/
theorem typedColorTable_eq_of_sourceRelabeling
    (I J : RootedIncidence hn rho) (currentType : C → A)
    (eC : Equiv.Perm C) (eS : Equiv.Perm S)
    (htype : ∀ c, currentType (eC c) = currentType c)
    (hcenter : ∀ x : Root C S,
      sumRelabeling eC eS (I.matching.1.1.center x) =
        J.matching.1.1.center (sumRelabeling eC eS x)) :
    I.typedColorTable currentType = J.typedColorTable currentType := by
  funext j a
  exact Nat.card_congr
    ((tableFiberRootEquiv I currentType j a).trans
      ((typedRootFiberEquivOfSourceRelabeling I J currentType eC eS htype hcenter j a).trans
        (tableFiberRootEquiv J currentType j a).symm))

/-- Equality of typed color tables is equivalent to membership in the same labelled source
orbit, expressed without introducing a quotient type. -/
theorem typedColorTable_eq_iff_exists_sourceRelabeling
    (I J : RootedIncidence hn rho) (currentType : C → A) :
    I.typedColorTable currentType = J.typedColorTable currentType ↔
      ∃ (eC : Equiv.Perm C) (eS : Equiv.Perm S),
        (∀ c, currentType (eC c) = currentType c) ∧
        ∀ x : Root C S,
          sumRelabeling eC eS (I.matching.1.1.center x) =
            J.matching.1.1.center (sumRelabeling eC eS x) := by
  constructor
  · exact I.exists_sourceRelabeling_of_typedColorTable_eq J currentType
  · rintro ⟨eC, eS, htype, hcenter⟩
    exact I.typedColorTable_eq_of_sourceRelabeling J currentType eC eS htype hcenter

end RootedIncidence

end

end VOA.RootedMatching
