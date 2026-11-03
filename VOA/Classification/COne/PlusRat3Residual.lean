import VOA.Classification.COne.PlusRat3Eight

/-! # The residual after the gap-one pairs

`RemainingAfterGapOne` is `RemainingUnordered` with every gap-one charged/charged pair (both rows
unique at their weights) removed, and with `m = 8` removed (proved in full).  It implies
`RemainingUnordered`, hence `V2mPlusRationalFactGe2`.  It is OPEN (true by Abe 2005, §7).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne
open PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- A gap-one charged/charged pair whose rows are unique at their weights. -/
def IsGapOneCharged (m : ℕ) (p : Label m × Label m) : Prop :=
  ∃ r r' : Fin (m - 1), p = (.inl r, .inl r') ∧ weight m (.inl r') = weight m (.inl r) + 1 ∧
    (∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r) ∧
    (∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r')

/-- OPEN (true by Abe 2005, §7): the obligations not covered by `PlusRat3`. -/
def RemainingAfterGapOne : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → m ≠ 8 → ∀ p ∈ positivePairs m,
    ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 → ¬ IsGapOneCharged m p → PairSplitting m hm p.1 p.2

/-- The gap-one pairs are discharged. -/
theorem pairSplitting_of_isGapOneCharged (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (p : Label m × Label m) (hp : IsGapOneCharged m p) : PairSplitting m hm p.1 p.2 := by
  obtain ⟨r, r', rfl, hgap, huq, huq'⟩ := hp
  exact (pairSplitting_charged_gap_one_both m hm hm2 r r' hgap huq huq').2

/-- `RemainingAfterGapOne → RemainingUnordered`. -/
theorem remainingUnordered_of_afterGapOne (h : RemainingAfterGapOne) : RemainingUnordered := by
  intro m hm hm2 p hp hvs hi
  by_cases h8 : m = 8
  · subst h8
    rcases positivePairs_eight_cert p hp with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hvs
    · exact absurd h1 hi
    · subst h1
      exact (pairSplitting_charged_gap_one_both 8 hm (by norm_num) 1 5 weight_eight_gap
        weight_eight_c2 weight_eight_c6).2
    · subst h1
      exact pairSplitting_swap 8 hm (by decide +kernel) (pairSplitting_half_sign_eight hm 2 (Or.inl rfl))
    · subst h1
      exact pairSplitting_swap 8 hm (by decide +kernel) (pairSplitting_half_sign_eight hm 3 (Or.inr rfl))
  by_cases hg : IsGapOneCharged m p
  · exact pairSplitting_of_isGapOneCharged m hm hm2 p hg
  · exact h m hm hm2 h8 p hp hvs hi hg

/-- The residual implies rationality of every `V_{2m}⁺`, `m ≥ 2`. -/
theorem rationality_of_remainingAfterGapOne (h : RemainingAfterGapOne) : V2mPlusRationalFactGe2 :=
  rationality_of_remainingUnordered (remainingUnordered_of_afterGapOne h)

end VOA.Classification.COne
