import VOA.Classification.COne.PlusRat2DualSwap

/-! # One orientation per pair suffices for `V_{2m}⁺`

`pairSplitting_swap`: by contragredient symmetry (`pairSplit_swap`), `PairSplitting m hm j i`
implies `PairSplitting m hm i j` whenever the two weights differ.  Consequences:

* `pairSplitting_vacuum_kernel`: every vacuum-kernel pair (kernel bottom `0`, quotient bottom an
  integer `≥ 2`) splits, the swap of the proved vacuum-quotient family.  This removes, e.g., the
  `m = 8` pairs `(vacuum, half±)`.
* `RemainingUnordered`: the residual needs only the orientation listed in `positivePairs`
  (lower weight in the kernel), for pairs avoiding the vacuum row and the vacuum/sign weights.
  It is equivalent to `RemainingPairObligations` and implies `V2mPlusRationalFactGe2`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat2
open PlusCharacterTable PlusResonantPairs PlusSplitting PlusRat2Dual

variable (m : ℕ) (hm : 1 ≤ m)

theorem pairSplitting_iff_pairSplit (i j : Label m) :
    PairSplitting m hm i j ↔ PairSplit (V2mPlus m hm) (weight m i : ℂ) (weight m j : ℂ) :=
  Iff.rfl

/-- **Swap symmetry** of the ordered obligations. -/
theorem pairSplitting_swap {i j : Label m} (hne : weight m i ≠ weight m j)
    (h : PairSplitting m hm j i) : PairSplitting m hm i j :=
  pairSplit_swap (V2mPlus_c2Cofinite m hm) (by exact_mod_cast hne) h

/-- Vacuum kernel, quotient of integral bottom `> 1`: splits. -/
theorem pairSplitting_vacuum_kernel (hm2 : 2 ≤ m) (i : Label m) (hi : 1 < weight m i) :
    PairSplitting m hm (.inr 0) i := by
  apply pairSplitting_swap m hm
  · have : weight m (.inr 0) = 0 := by simp [weight]
    rw [this]; intro h; rw [← h] at hi; norm_num at hi
  · exact pairSplitting_vacuum_quotient_of_gt_one m hm hm2 i hi

theorem isVacuumSignWeights_swap {p : Label m × Label m} (h : IsVacuumSignWeights m p.swap) :
    IsVacuumSignWeights m p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

theorem weight_ne_of_positive {i j : Label m} (h : (i, j) ∈ positivePairs m) :
    weight m i ≠ weight m j := by
  simp only [positivePairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  intro he
  rw [he, sub_self] at h
  exact lt_irrefl 0 h.1

theorem weight_vacuum : weight m (.inr 0) = 0 := by simp [weight]

/-- Per-`m` reduction to one orientation per non-vacuum, non-vacuum/sign pair. -/
theorem remaining_of_unordered (hm2 : 2 ≤ m)
    (h : ∀ p ∈ positivePairs m, ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 →
      PairSplitting m hm p.1 p.2) :
    ∀ q ∈ remainingOrientedPairs m, PairSplitting m hm q.1 q.2 := by
  rintro ⟨i, j⟩ hq
  obtain ⟨hpos, hnot⟩ := (mem_remainingOrientedPairs_iff m i j).mp hq
  by_cases hvs : IsVacuumSignWeights m (i, j)
  · exact pairSplitting_of_vacuumSignWeights m hm hm2 (i, j) hvs
  rcases hpos with hp | hp
  · -- `(i, j)` itself is listed: kernel has the lower weight
    by_cases hi : i = .inr 0
    · subst hi
      apply pairSplitting_vacuum_kernel m hm hm2 j
      obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m _ _).mp hp
      rw [weight_vacuum] at he
      have hwj : weight m j = (z : ℚ) := by
        apply Rat.cast_injective (α := ℂ); push_cast; simpa using he
      rcases lt_or_eq_of_le (show (1 : ℤ) ≤ z by omega) with hz1 | hz1
      · rw [hwj]; exact_mod_cast hz1
      · exfalso
        apply hvs
        left
        exact ⟨weight_vacuum m, by rw [hwj, ← hz1]; norm_num⟩
    · exact h (i, j) hp hvs hi
  · -- `(j, i)` is listed: swap
    apply pairSplitting_swap m hm (Ne.symm (weight_ne_of_positive m hp))
    by_cases hj : j = .inr 0
    · exfalso
      subst hj
      obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m _ _).mp hp
      rw [weight_vacuum] at he
      have hwi : weight m i = (z : ℚ) := by
        apply Rat.cast_injective (α := ℂ); push_cast; simpa using he
      rcases lt_or_eq_of_le (show (1 : ℤ) ≤ z by omega) with hz1 | hz1
      · exact hnot ⟨rfl, by rw [hwi]; exact_mod_cast hz1⟩
      · apply hvs
        right
        exact ⟨by rw [hwi, ← hz1]; norm_num, weight_vacuum m⟩
    · exact h (j, i) hp (fun h' => hvs (isVacuumSignWeights_swap m h')) hj

/-- Per-`m` strong rationality from one orientation per remaining pair. -/
theorem V2mPlus_stronglyRational_of_unordered (hm2 : 2 ≤ m)
    (h : ∀ p ∈ positivePairs m, ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 →
      PairSplitting m hm p.1 p.2) :
    StronglyRational (V2mPlus m hm) :=
  { OrbRat.V2mPlus_stronglyFinite m hm with
    rational := PlusRatSign.admissiblyRational_of_remaining m hm hm2
      (remaining_of_unordered m hm hm2 h) }

end VOA.Classification.COne.PlusRat2

namespace VOA.Classification.COne
open PlusCharacterTable PlusResonantPairs PlusRat2

/-- OPEN, TRUE (Abe 2005, §7): one orientation (the listed one, lower weight in the kernel) of
every positive integral gap that avoids the vacuum row and the vacuum/sign weights. -/
def RemainingUnordered : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ p ∈ positivePairs m,
    ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 → PairSplitting m hm p.1 p.2

/-- The reduction is exact. -/
theorem remainingUnordered_iff : RemainingUnordered ↔ RemainingPairObligations := by
  constructor
  · intro h m hm hm2
    exact remaining_of_unordered m hm hm2 (h m hm hm2)
  · intro h m hm hm2 p hp _ _
    apply h m hm hm2 p
    exact (mem_remainingOrientedPairs_iff m p.1 p.2).mpr ⟨Or.inl hp, by
      rintro ⟨h2, -⟩
      have := (mem_positivePairs_iff m _ _).mp hp
      obtain ⟨z, hz, he⟩ := this
      rw [h2, weight_vacuum] at he
      have hw : (weight m p.1 : ℂ) = -(z : ℂ) := by linear_combination -he
      have hw' : weight m p.1 = -(z : ℚ) := by
        apply Rat.cast_injective (α := ℂ); push_cast; exact hw
      have hnn : 0 ≤ weight m p.1 := by
        rcases p.1 with r | i
        · simp only [weight]; positivity
        · fin_cases i <;> norm_num [weight] <;> positivity
      rw [hw'] at hnn
      have : (0 : ℚ) < z := by exact_mod_cast hz
      linarith⟩

/-- `V_{2m}⁺` rationality from one orientation per remaining pair. -/
theorem rationality_of_remainingUnordered (h : RemainingUnordered) : V2mPlusRationalFactGe2 :=
  rationality_of_remainingPairObligations (remainingUnordered_iff.mp h)

end VOA.Classification.COne

namespace VOA.Classification.COne.PlusRat2
open PlusCharacterTable PlusResonantPairs

/-- At `m = 6` the only positive integral gap avoiding the vacuum row and the vacuum/sign
weights is the charged pair `(s = 1, s = 5)`, of weights `1/24` and `25/24`. -/
theorem positivePairs_six (i j : Label 6) (h : (i, j) ∈ positivePairs 6) :
    IsVacuumSignWeights 6 (i, j) ∨ i = .inr 0 ∨ (i = .inl 0 ∧ j = .inl 4) := by
  simp only [positivePairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  unfold IsVacuumSignWeights
  rcases i with r | i <;> rcases j with t | j
  · fin_cases r <;> fin_cases t
    all_goals (try norm_num [weight] at h)
    all_goals norm_num [weight]
    exact Or.inr rfl
  · fin_cases r <;> fin_cases j
    all_goals (try norm_num [weight] at h)
  · fin_cases i <;> fin_cases t
    all_goals (try norm_num [weight] at h)
  · fin_cases i <;> fin_cases j
    all_goals (try norm_num [weight] at h)
    all_goals norm_num [weight]

/-- **`V_{12}⁺` (`m = 6`) is strongly rational as soon as the single charged pair
`(s = 1 kernel, s = 5 quotient)` splits.** -/
theorem V2mPlus_stronglyRational_six_of (hm : 1 ≤ 6)
    (h : PairSplitting 6 hm (.inl 0) (.inl 4)) : StronglyRational (V2mPlus 6 hm) := by
  apply V2mPlus_stronglyRational_of_unordered 6 hm (by norm_num)
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_six i j hp with h1 | h1 | ⟨rfl, rfl⟩
  · exact absurd h1 hvs
  · exact absurd h1 hi
  · exact h

end VOA.Classification.COne.PlusRat2
