/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Canonical words for finite multiplicities

Sorting a multiplicity multiset gives the ordered word used by creation
bases. Its commutative evaluation is the product of powers prescribed
by the multiplicities, independently of the chosen linear order.
-/
namespace VOA
noncomputable section
variable {α : Type*} [LinearOrder α]

/-- The increasing word in which each letter occurs with its prescribed
finite multiplicity. -/
def orderedExponentWord (e : α →₀ ℕ) : List α :=
  e.toMultiset.sort (· ≤ ·)

/-- Forgetting order recovers exactly the original multiplicities. -/
theorem orderedExponentWord_multiset (e : α →₀ ℕ) :
    (orderedExponentWord e : Multiset α)=e.toMultiset := Multiset.sort_eq _ _

/-- The canonical multiplicity word is increasing, with repetitions. -/
theorem orderedExponentWord_pairwise (e : α →₀ ℕ) :
    (orderedExponentWord e).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _

/-- Any increasing list is the canonical word of its multiplicities. -/
theorem orderedExponentWord_of_sorted (l : List α) (hl : l.Pairwise (· ≤ ·)) :
    orderedExponentWord (Multiset.toFinsupp (l : Multiset α))=l := by
  have h : (orderedExponentWord (Multiset.toFinsupp (l : Multiset α)) : Multiset α) = l := by
    rw [orderedExponentWord_multiset,Multiset.toFinsupp_toMultiset]
  exact (Multiset.coe_eq_coe.mp h).eq_of_pairwise' (orderedExponentWord_pairwise _) hl

/-- Evaluation in any commutative monoid forgets the ordering and
becomes the finite product of letter values to their multiplicities. -/
theorem orderedExponentWord_prod {R : Type*} [CommMonoid R] (e : α →₀ ℕ) (f : α → R) :
    ((orderedExponentWord e).map f).prod=e.prod (fun a n => f a ^ n) := by
  change (Multiset.map f (orderedExponentWord e : Multiset α)).prod=_
  rw [orderedExponentWord_multiset,Finsupp.toMultiset_map,Finsupp.prod_toMultiset]
  exact Finsupp.prod_mapDomain_index (by simp) (by intros; exact pow_add _ _ _)

end
end VOA
