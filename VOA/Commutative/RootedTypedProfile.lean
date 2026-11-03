/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.SetTheory.Cardinal.Finite
import VOA.Commutative.RootedProfile

/-!
# Typed counts inside a rooted profile

The coarse rooted profile records the number of all roots of each additional-`S`-leaf color.
This file decomposes that count according to the species of the root: a current root or an
`S`-particle root.  It also proves the elementary total-count identities needed to compare the
coarse component fiber with the sectors of the finite carrier.

These typed counts are auxiliary data attached to a labelled matching.  No claim is made that a
coarse profile fiber is a single species-preserving orbit, or that the typed counts classify such
orbits.
-/

namespace VOA.RootedMatching

noncomputable section

universe u v

variable {C : Type u} {S : Type v}

/-- The number of current-rooted blocks with exactly `j` additional `S`-leaves. -/
def currentRootProfileOf [Finite C] [Finite S] {n : ℕ}
    (m : AdmissibleRootedMatching n C S) : Fin n → ℕ :=
  fun j =>
    {c : C |
      m.1.IsRoot (.inl c) ∧ m.1.additionalSLeafCount (.inl c) = (j : ℕ)}.ncard

/-- The number of `S`-rooted blocks with exactly `j` additional `S`-leaves. -/
def sRootProfileOf [Finite C] [Finite S] {n : ℕ}
    (m : AdmissibleRootedMatching n C S) : Fin n → ℕ :=
  fun j =>
    {s : S |
      m.1.IsRoot (.inr s) ∧ m.1.additionalSLeafCount (.inr s) = (j : ℕ)}.ncard

/-- The number of retained `S` roots of a labelled matching. -/
def sRootCount [Finite S] (m : RawRootedMatching C S) : ℕ :=
  {s : S | m.IsRoot (.inr s)}.ncard

/-- The total number of roots, equivalently the number of blocks. -/
def totalRootCount [Finite C] [Finite S] (m : RawRootedMatching C S) : ℕ :=
  {r : Root C S | m.IsRoot r}.ncard

/-- The coarse color count is the sum of its current-rooted and `S`-rooted parts. -/
theorem profileOf_eq_currentRootProfileOf_add_sRootProfileOf [Finite C] [Finite S] {n : ℕ}
    (m : AdmissibleRootedMatching n C S) (j : Fin n) :
    profileOf m j = currentRootProfileOf m j + sRootProfileOf m j := by
  change Nat.card {r : Root C S //
      m.1.IsRoot r ∧ m.1.additionalSLeafCount r = (j : ℕ)} =
    Nat.card {c : C //
      m.1.IsRoot (.inl c) ∧ m.1.additionalSLeafCount (.inl c) = (j : ℕ)} +
    Nat.card {s : S //
      m.1.IsRoot (.inr s) ∧ m.1.additionalSLeafCount (.inr s) = (j : ℕ)}
  rw [← Nat.card_sum]
  exact Nat.card_congr Equiv.subtypeSum

/-- Every current is a root, so the total number of roots is the number of currents plus the
number of retained `S` roots. -/
theorem totalRootCount_eq_card_add_sRootCount [Finite C] [Finite S]
    (m : RawRootedMatching C S) :
    totalRootCount m = Nat.card C + sRootCount m := by
  change Nat.card {r : Root C S // m.IsRoot r} =
    Nat.card C + Nat.card {s : S // m.IsRoot (.inr s)}
  rw [← Nat.card_sum]
  refine Nat.card_congr (Equiv.subtypeSum.trans (Equiv.sumCongr ?_ (Equiv.refl _)))
  exact
    { toFun := fun c => c.1
      invFun := fun c => ⟨c, m.current_isRoot c⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private def currentColor [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (c : C) : Fin n :=
  ⟨m.1.additionalSLeafCount (.inl c), additionalSLeafCount_lt hn m (.inl c)⟩

private def sRootColor [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (s : {s : S // m.1.IsRoot (.inr s)}) : Fin n :=
  ⟨m.1.additionalSLeafCount (.inr s.1), additionalSLeafCount_lt hn m (.inr s.1)⟩

private def sRootFiberEquiv [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) (j : Fin n) :
    {s : S | m.1.IsRoot (.inr s) ∧
        m.1.additionalSLeafCount (.inr s) = (j : ℕ)} ≃
      {s : {s : S // m.1.IsRoot (.inr s)} // sRootColor hn m s = j} where
  toFun s := ⟨⟨s.1, s.2.1⟩, Fin.ext s.2.2⟩
  invFun s := ⟨s.1.1, s.1.2, congrArg Fin.val s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Under `0 < n`, the current-root color classes exhaust all currents. -/
theorem sum_currentRootProfileOf_eq_card [Finite C] [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) :
    ∑ j : Fin n, currentRootProfileOf m j = Nat.card C := by
  let f := currentColor hn m
  calc
    ∑ j : Fin n, currentRootProfileOf m j =
        ∑ j : Fin n, Nat.card {c : C // f c = j} := by
          apply Finset.sum_congr rfl
          intro j _
          apply Nat.card_congr
          exact Equiv.subtypeEquivRight fun c => by
            change (m.1.IsRoot (.inl c) ∧
                m.1.additionalSLeafCount (.inl c) = (j : ℕ)) ↔ f c = j
            rw [and_iff_right (m.1.current_isRoot c)]
            constructor
            · exact fun h => Fin.ext h
            · exact fun h => congrArg Fin.val h
    _ = Nat.card (Sigma fun j : Fin n => {c : C // f c = j}) := Nat.card_sigma.symm
    _ = Nat.card C := Nat.card_congr (Equiv.sigmaFiberEquiv f)

/-- Under `0 < n`, the `S`-root color classes exhaust all retained `S` roots. -/
theorem sum_sRootProfileOf_eq_sRootCount [Finite C] [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) :
    ∑ j : Fin n, sRootProfileOf m j = sRootCount m.1 := by
  let T := {s : S // m.1.IsRoot (.inr s)}
  let f : T → Fin n := sRootColor hn m
  calc
    ∑ j : Fin n, sRootProfileOf m j =
        ∑ j : Fin n, Nat.card {s : T // f s = j} := by
          apply Finset.sum_congr rfl
          intro j _
          apply Nat.card_congr
          exact sRootFiberEquiv hn m j
    _ = Nat.card (Sigma fun j : Fin n => {s : T // f s = j}) := Nat.card_sigma.symm
    _ = Nat.card T := Nat.card_congr (Equiv.sigmaFiberEquiv f)
    _ = sRootCount m.1 := rfl

/-- Under `0 < n`, summing the coarse profile counts every block exactly once. -/
theorem sum_profileOf_eq_totalRootCount [Finite C] [Finite S] {n : ℕ} (hn : 0 < n)
    (m : AdmissibleRootedMatching n C S) :
    ∑ j : Fin n, profileOf m j = totalRootCount m.1 := by
  simp_rw [profileOf_eq_currentRootProfileOf_add_sRootProfileOf m]
  rw [Finset.sum_add_distrib, sum_currentRootProfileOf_eq_card hn m,
    sum_sRootProfileOf_eq_sRootCount hn m, totalRootCount_eq_card_add_sRootCount]

end

end VOA.RootedMatching
