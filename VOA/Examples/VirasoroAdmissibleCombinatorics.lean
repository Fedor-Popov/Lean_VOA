/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPartitionBasis

/-!
# Admissible partitions for the boundary Virasoro models

This file contains only the finite combinatorics underlying Salazar's boundary-model basis
theorem.  It does **not** assert that admissible monomials form a basis of the simple quotient.

## Convention

A repository word `w = [w₀, ..., wᵣ₋₁]` represents the partition
`λ = (w₀ + 2, ..., wᵣ₋₁ + 2)` and the creation monomial
`L₋(w₀+2) ... L₋(wᵣ₋₁+2)|0⟩`.  Thus Salazar's vacuum admissibility condition for the boundary
model `L(c_{2,2n+1},0)`,

`λⱼ - λⱼ₊ₙ₋₁ ≥ 2`,

translates without any extra shift to

`wⱼ ≥ wⱼ₊ₙ₋₁ + 2`.

The definition below is meaningful for every natural `n`; applications to boundary minimal
models assume `2 ≤ n`.

## Contents

* `IsNAdmissible` -- the distance-`n-1` difference condition on repository words;
* `AdmissibleOfEnergy`, `AdmissibleOfEnergyLength` -- finite index types;
* `admissibleCount` -- the exact finite count by energy and length;
* elementary classifications and counts in lengths zero, one, and two.

No PBW theorem, quotient-module theorem, or project axiom is used.
-/

set_option linter.style.longLine false

namespace VOA

namespace AdmissiblePartitions

open VOA.VirModule

/-! ## The predicate and finite index types -/

/-- Salazar's `n`-admissibility condition in the repository's shifted word convention.

For every window of `n` consecutive parts, the first and last differ by at least two.  The
application range is `2 ≤ n`; retaining a total definition is convenient for finite computation.
-/
def IsNAdmissible (n : ℕ) (w : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i + (n - 1) < w.length),
    w.get ⟨i, by omega⟩ ≥ w.get ⟨i + (n - 1), hi⟩ + 2

/-- Classical decision of the spacing condition permits finite filtering. It does not supply a faster numerical admissibility algorithm. -/
noncomputable instance (n : ℕ) (w : List ℕ) : Decidable (IsNAdmissible n w) :=
  Classical.propDecidable _

/-- Sorted admissible words of fixed conformal energy. -/
def AdmissibleOfEnergy (n N : ℕ) : Type :=
  {w : SortedOfEnergy N // IsNAdmissible n w.1}

/-- Equality of fixed-energy admissible partitions is inherited from their underlying finite words; proof witnesses do not affect equality. -/
instance (n N : ℕ) : DecidableEq (AdmissibleOfEnergy n N) := Subtype.instDecidableEq

/-- Enumerate admissible words by filtering the already finite set of all partitions of this energy. This proves the combinatorial count is finite. -/
noncomputable instance (n N : ℕ) : Fintype (AdmissibleOfEnergy n N) := by
  classical
  letI := sortedOfEnergyFintype N
  exact Fintype.subtype
    (Finset.univ.filter fun w : SortedOfEnergy N => IsNAdmissible n w.1) (by simp)

/-- Sorted admissible words of fixed conformal energy and exact creation-word length. -/
def AdmissibleOfEnergyLength (n N r : ℕ) : Type :=
  {w : AdmissibleOfEnergy n N // w.1.1.length = r}

/-- Two exact-length indices are equal precisely when their underlying admissible words agree. -/
instance (n N r : ℕ) : DecidableEq (AdmissibleOfEnergyLength n N r) :=
  Subtype.instDecidableEq

/-- Imposing an exact word length selects a finite subset of the admissible partitions at fixed energy. -/
noncomputable instance (n N r : ℕ) : Fintype (AdmissibleOfEnergyLength n N r) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun w : AdmissibleOfEnergy n N => w.1.1.length = r) (by simp)

/-- The number of `n`-admissible partitions of energy `N` and exact length `r`. -/
noncomputable def admissibleCount (n N r : ℕ) : ℕ :=
  Fintype.card (AdmissibleOfEnergyLength n N r)

/-- Admissible words of fixed energy and length at most `p`. -/
def AdmissibleOfEnergyLengthLE (n N p : ℕ) : Type :=
  {w : AdmissibleOfEnergy n N // w.1.1.length ≤ p}

/-- The length bound adds a proposition to a word, so equality is still decided on the underlying word. -/
instance (n N p : ℕ) : DecidableEq (AdmissibleOfEnergyLengthLE n N p) :=
  Subtype.instDecidableEq

/-- Filtering the finite admissible family by the maximum word length produces the finite set counted by the cumulative filtration count. -/
noncomputable instance (n N p : ℕ) : Fintype (AdmissibleOfEnergyLengthLE n N p) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun w : AdmissibleOfEnergy n N => w.1.1.length ≤ p) (by simp)

/-- The cumulative admissible count in filtration degrees at most `p`. -/
noncomputable def admissibleCumulativeCount (n N p : ℕ) : ℕ :=
  Fintype.card (AdmissibleOfEnergyLengthLE n N p)

/-- Partition the bounded-length admissible words by their exact length. -/
noncomputable def admissibleLengthLEEquivSigma (n N p : ℕ) :
    AdmissibleOfEnergyLengthLE n N p ≃
      Σ r : Fin (p + 1), AdmissibleOfEnergyLength n N r.1 where
  toFun w := ⟨⟨w.1.1.1.length, Nat.lt_succ_of_le w.2⟩, ⟨w.1, rfl⟩⟩
  invFun w := ⟨w.2.1, by rw [w.2.2]; exact Nat.le_of_lt_succ w.1.2⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    rcases w with ⟨⟨r, hr⟩, ⟨w, hw⟩⟩
    change w.1.1.length = r at hw
    subst r
    rfl

/-- The cumulative count is the sum of the exact-length counts. -/
theorem admissibleCumulativeCount_eq_sum (n N p : ℕ) :
    admissibleCumulativeCount n N p =
      ∑ r ∈ Finset.range (p + 1), admissibleCount n N r := by
  rw [admissibleCumulativeCount,
    Fintype.card_congr (admissibleLengthLEEquivSigma n N p), Fintype.card_sigma,
    Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp : r ≤ p := by simp at hr; omega
  simp [admissibleCount, hrp]

/-! ## Elementary admissibility lemmas -/

/-- A word shorter than the window size is automatically admissible. -/
theorem isNAdmissible_of_length_lt {n : ℕ} {w : List ℕ} (h : w.length < n) :
    IsNAdmissible n w := by
  intro i hi
  omega

/-- Every word of length at most one is admissible for boundary indices `n ≥ 2`. -/
theorem isNAdmissible_of_length_le_one {n : ℕ} (hn : 2 ≤ n) {w : List ℕ}
    (hw : w.length ≤ 1) : IsNAdmissible n w :=
  isNAdmissible_of_length_lt (by omega)

/-- Every word of length at most two is admissible when `n ≥ 3`. -/
theorem isNAdmissible_of_length_le_two {n : ℕ} (hn : 3 ≤ n) {w : List ℕ}
    (hw : w.length ≤ 2) : IsNAdmissible n w :=
  isNAdmissible_of_length_lt (by omega)

/-- The empty creation word satisfies every window admissibility condition because it contains no window to test. It represents the vacuum in the combinatorial count. -/
@[simp] theorem isNAdmissible_nil (n : ℕ) : IsNAdmissible n [] := by
  intro i hi
  simp at hi

/-- A single creation mode is admissible whenever the forbidden window has size at least two. There are not enough entries for the spacing condition to impose a restriction. -/
@[simp] theorem isNAdmissible_singleton {n a : ℕ} (hn : 2 ≤ n) :
    IsNAdmissible n [a] :=
  isNAdmissible_of_length_le_one hn (by simp)

/-- At the Lee--Yang boundary index `n = 2`, a two-part word is admissible precisely when its
two (shifted) entries differ by at least two. -/
@[simp] theorem isNAdmissible_two_pair (a b : ℕ) :
    IsNAdmissible 2 [a, b] ↔ b + 2 ≤ a := by
  constructor
  · intro h
    simpa [IsNAdmissible] using h 0 (by simp)
  · intro hab i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [IsNAdmissible] using hab

/-! ## Length zero and one -/

/-- A word of length zero and energy `N` exists exactly at `N = 0`. -/
theorem admissibleOfEnergyLength_zero_iff {n N : ℕ}
    (w : AdmissibleOfEnergyLength n N 0) : N = 0 := by
  have hw : w.1.1.1 = [] := List.length_eq_zero_iff.mp w.2
  have henergy := w.1.1.2.2
  simpa [hw] using henergy.symm

/-- There is exactly one admissible word with zero energy and zero length: the empty word. This fixes the vacuum coefficient of the counting series. -/
@[simp] theorem admissibleCount_zero_zero (n : ℕ) : admissibleCount n 0 0 = 1 := by
  rw [admissibleCount, Fintype.card_eq_one_iff]
  let w0 : AdmissibleOfEnergyLength n 0 0 :=
    ⟨⟨⟨[], sortedWord_nil, rfl⟩, isNAdmissible_nil n⟩, rfl⟩
  refine ⟨w0, fun w => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact List.length_eq_zero_iff.mp w.2

/-- A word of zero length has zero energy. Thus no such word contributes to any nonzero energy, independently of the admissibility parameter. -/
@[simp] theorem admissibleCount_zero_of_ne_zero (n N : ℕ) (hN : N ≠ 0) :
    admissibleCount n N 0 = 0 := by
  letI : IsEmpty (AdmissibleOfEnergyLength n N 0) :=
    ⟨fun w => hN (admissibleOfEnergyLength_zero_iff w)⟩
  exact Fintype.card_eq_zero

/-- A fixed-energy singleton is unique. -/
theorem admissibleOfEnergyLength_one_unique {n N : ℕ}
    (x y : AdmissibleOfEnergyLength n N 1) : x = y := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp x.2
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp y.2
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [ha, hb]
  have hx : energyVir x.1.1.1 = N := x.1.1.2.2
  have hy : energyVir y.1.1.1 = N := y.1.1.2.2
  rw [ha] at hx
  rw [hb] at hy
  change a + 2 = N at hx
  change b + 2 = N at hy
  congr 1
  omega

/-- For every boundary index, there is one admissible singleton at every energy `N ≥ 2`. -/
theorem admissibleCount_one_of_two_le {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N) :
    admissibleCount n N 1 = 1 := by
  rw [admissibleCount, Fintype.card_eq_one_iff]
  let w : AdmissibleOfEnergyLength n N 1 :=
    ⟨⟨⟨[N - 2], sortedWord_singleton _, by simp [energyVir]; omega⟩,
        isNAdmissible_singleton hn⟩, by simp⟩
  exact ⟨w, fun y => admissibleOfEnergyLength_one_unique y w⟩

/-- No singleton has energy below two. -/
theorem admissibleCount_one_of_lt_two (n N : ℕ) (hN : N < 2) :
    admissibleCount n N 1 = 0 := by
  letI : IsEmpty (AdmissibleOfEnergyLength n N 1) := ⟨fun w => by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp w.2
    have henergy := w.1.1.2.2
    simp [ha, energyVir] at henergy
    omega⟩
  exact Fintype.card_eq_zero

/-- Closed singleton count for the boundary range `n ≥ 2`. -/
theorem admissibleCount_one {n N : ℕ} (hn : 2 ≤ n) :
    admissibleCount n N 1 = if 2 ≤ N then 1 else 0 := by
  split_ifs with hN
  · exact admissibleCount_one_of_two_le hn hN
  · exact admissibleCount_one_of_lt_two n N (by omega)

/-! ## Length two: classifications -/

/-- A sorted word of exact length two has a unique presentation `[a,b]` with `b ≤ a`. -/
theorem exists_eq_pair_of_length_two {N : ℕ} (w : SortedOfEnergy N)
    (hlen : w.1.length = 2) :
    ∃ a b : ℕ, w.1 = [a, b] ∧ b ≤ a ∧ a + b + 4 = N := by
  rcases w with ⟨l, hsort, henergy⟩
  cases l with
  | nil => simp at hlen
  | cons a tail =>
      cases tail with
      | nil => simp at hlen
      | cons b tail' =>
          cases tail' with
          | nil =>
              refine ⟨a, b, rfl, ?_, ?_⟩
              · simpa [SortedWord] using hsort
              · simpa [energyVir, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using henergy
          | cons c tail'' => simp at hlen

/-- At `n ≥ 3`, the admissibility constraint is vacuous in exact length two. -/
theorem isNAdmissible_length_two_of_three_le {n N : ℕ} (hn : 3 ≤ n)
    (w : SortedOfEnergy N) (hlen : w.1.length = 2) : IsNAdmissible n w.1 :=
  isNAdmissible_of_length_le_two hn hlen.le

/-- At `n = 2`, exact-length-two admissibility adds the strict two-step gap to sortedness. -/
theorem admissible_pair_leeYang_iff (a b : ℕ) :
    SortedWord [a, b] ∧ IsNAdmissible 2 [a, b] ↔ b + 2 ≤ a := by
  constructor
  · exact fun h => isNAdmissible_two_pair a b |>.mp h.2
  · intro h
    refine ⟨?_, isNAdmissible_two_pair a b |>.mpr h⟩
    simpa [SortedWord] using (show b ≤ a by omega)

/-! ## Length two: exact counts -/

/-- The second (smaller) shifted part of an exact-length-two admissible word. -/
def lengthTwoSecond {n N : ℕ} (w : AdmissibleOfEnergyLength n N 2) : ℕ :=
  w.1.1.1.get ⟨1, by simp [w.2]⟩

/-- Once an admissible length-two word is written as [a,b], its extracted
smaller part is exactly b. This connects the dependent list accessor to
the ordinary pair coordinates used in the counting argument. -/
theorem lengthTwoSecond_eq {n N a b : ℕ} (w : AdmissibleOfEnergyLength n N 2)
    (hw : w.1.1.1 = [a, b]) : lengthTwoSecond w = b := by
  simp [lengthTwoSecond, hw]

/-- In the range where length-two admissibility is vacuous, the smaller part lies in the finite
interval of size `N / 2 - 1`. -/
theorem lengthTwoSecond_lt {n N : ℕ}
    (w : AdmissibleOfEnergyLength n N 2) : lengthTwoSecond w < N / 2 - 1 := by
  obtain ⟨a, b, hw, hba, henergy⟩ := exists_eq_pair_of_length_two w.1.1 w.2
  rw [lengthTwoSecond_eq w hw]
  omega

/-- The exact-length-two admissible words for `n ≥ 3`, reindexed by their smaller part. -/
noncomputable def admissibleLengthTwoEquivFin {n N : ℕ} (hn : 3 ≤ n) (hN : 4 ≤ N) :
    AdmissibleOfEnergyLength n N 2 ≃ Fin (N / 2 - 1) := by
  let f : AdmissibleOfEnergyLength n N 2 → Fin (N / 2 - 1) := fun w =>
    ⟨lengthTwoSecond w, lengthTwoSecond_lt w⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, b, hx, hba, hxenergy⟩ := exists_eq_pair_of_length_two x.1.1 x.2
    obtain ⟨a', b', hy, hb'a', hyenergy⟩ := exists_eq_pair_of_length_two y.1.1 y.2
    have hbb' : b = b' := by
      simpa [f, lengthTwoSecond_eq x hx, lengthTwoSecond_eq y hy] using congrArg Fin.val hxy
    have haa' : a = a' := by omega
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simp [hx, hy, hbb', haa']
  · intro b
    let a : ℕ := N - 4 - b.1
    have hba : b.1 ≤ a := by
      dsimp [a]
      omega
    have henergy : a + b.1 + 4 = N := by
      dsimp [a]
      omega
    let w : AdmissibleOfEnergyLength n N 2 :=
      ⟨⟨⟨[a, b.1], by simpa [SortedWord] using hba, by
            simp only [energyVir]
            omega⟩,
          isNAdmissible_of_length_le_two hn (by simp)⟩, by simp⟩
    refine ⟨w, ?_⟩
    apply Fin.ext
    simp [f, w, lengthTwoSecond, a]

/-- For `n ≥ 3`, every two-part partition is admissible, giving the universal count
`⌊N/2⌋ - 1` at energy `N ≥ 4`. -/
theorem admissibleCount_two_of_three_le {n N : ℕ} (hn : 3 ≤ n) (hN : 4 ≤ N) :
    admissibleCount n N 2 = N / 2 - 1 := by
  rw [admissibleCount]
  exact (Fintype.card_congr (admissibleLengthTwoEquivFin hn hN)).trans (Fintype.card_fin _)

/-- In the Lee--Yang case, the smaller part lies in the shorter interval of size
`N / 2 - 2`, reflecting the required gap of two. -/
theorem lengthTwoSecond_lt_leeYang {N : ℕ}
    (w : AdmissibleOfEnergyLength 2 N 2) : lengthTwoSecond w < N / 2 - 2 := by
  obtain ⟨a, b, hw, hba, henergy⟩ := exists_eq_pair_of_length_two w.1.1 w.2
  have hadm : b + 2 ≤ a := by
    apply (isNAdmissible_two_pair a b).mp
    simpa [hw] using w.1.2
  rw [lengthTwoSecond_eq w hw]
  omega

/-- The exact-length-two Lee--Yang admissible words, reindexed by their smaller part. -/
noncomputable def leeYangAdmissibleLengthTwoEquivFin {N : ℕ} (hN : 4 ≤ N) :
    AdmissibleOfEnergyLength 2 N 2 ≃ Fin (N / 2 - 2) := by
  let f : AdmissibleOfEnergyLength 2 N 2 → Fin (N / 2 - 2) := fun w =>
    ⟨lengthTwoSecond w, lengthTwoSecond_lt_leeYang w⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, b, hx, hba, hxenergy⟩ := exists_eq_pair_of_length_two x.1.1 x.2
    obtain ⟨a', b', hy, hb'a', hyenergy⟩ := exists_eq_pair_of_length_two y.1.1 y.2
    have hbb' : b = b' := by
      simpa [f, lengthTwoSecond_eq x hx, lengthTwoSecond_eq y hy] using congrArg Fin.val hxy
    have haa' : a = a' := by omega
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simp [hx, hy, hbb', haa']
  · intro b
    let a : ℕ := N - 4 - b.1
    have hgap : b.1 + 2 ≤ a := by
      dsimp [a]
      omega
    have henergy : a + b.1 + 4 = N := by
      dsimp [a]
      omega
    let w : AdmissibleOfEnergyLength 2 N 2 :=
      ⟨⟨⟨[a, b.1], by
              simpa [SortedWord] using (show b.1 ≤ a by omega), by
            simp only [energyVir]
            omega⟩,
          (isNAdmissible_two_pair a b.1).mpr hgap⟩, by simp⟩
    refine ⟨w, ?_⟩
    apply Fin.ext
    simp [f, w, lengthTwoSecond, a]

/-- The Lee--Yang exact-length-two count is one below the universal count. -/
theorem admissibleCount_two_leeYang {N : ℕ} (hN : 4 ≤ N) :
    admissibleCount 2 N 2 = N / 2 - 2 := by
  rw [admissibleCount]
  exact (Fintype.card_congr (leeYangAdmissibleLengthTwoEquivFin hN)).trans (Fintype.card_fin _)

/-- No word of exact length two has energy below four. -/
theorem admissibleCount_two_of_lt_four (n N : ℕ) (hN : N < 4) :
    admissibleCount n N 2 = 0 := by
  letI : IsEmpty (AdmissibleOfEnergyLength n N 2) := ⟨fun w => by
    obtain ⟨a, b, hw, hba, henergy⟩ := exists_eq_pair_of_length_two w.1.1 w.2
    omega⟩
  exact Fintype.card_eq_zero

/-- Closed exact-length-two count for all boundary indices `n ≥ 2`. -/
theorem admissibleCount_two {n N : ℕ} (hn : 2 ≤ n) :
    admissibleCount n N 2 =
      if n = 2 then N / 2 - 2 else N / 2 - 1 := by
  by_cases hN : N < 4
  · rw [admissibleCount_two_of_lt_four n N hN]
    have hhalf : N / 2 ≤ 1 := by omega
    split_ifs <;> omega
  · have hN4 : 4 ≤ N := by omega
    by_cases hn2 : n = 2
    · subst hn2
      rw [if_pos rfl]
      exact admissibleCount_two_leeYang hN4
    · rw [if_neg hn2]
      exact admissibleCount_two_of_three_le (by omega) hN4

end AdmissiblePartitions

end VOA
