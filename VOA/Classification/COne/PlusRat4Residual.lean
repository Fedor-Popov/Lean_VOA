import VOA.Classification.COne.PlusRat4Nine
import VOA.Classification.COne.PlusRat4Twelve

/-! # The residual after the gap-two pairs

* `IsQuarterPair m p`: `p = (c_s, i)` with `h_s = 1/4`, `s ≤ m - 3`, `m ≥ 5`, `weight i = 9/4`,
  `c_s` unique at `1/4`, no row of weight `5/4` (`pairSplitting_of_isQuarterPair`).
* `RemainingAfterGapTwo` (OPEN, true by Abe 2005 §7): `RemainingAfterGapOne` with `m = 9, 10, 12`
  removed and with the gap-two charged pairs and the quarter pairs removed.
* `remainingAfterGapOne_of_afterGapTwo`, `rationality_of_remainingAfterGapTwo`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- Every row of weight `9/4` kills `H⁴` (it is charged or half). -/
theorem chiT_ninefour_H4 (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (j : Label m)
    (hj : weight m j = 9 / 4) :
    chiT m hm hm2 j (VOA.mk (V2mPlus m hm) (HP m hm 2)) = 0 := by
  rcases j with r | i
  · exact chiT_HP_zero m hm hm2 r 2 (Or.inl rfl)
  · fin_cases i <;>
      first
      | exact chiT_half_HP_zero m hm hm2 2 (Or.inl rfl) 2 (Or.inl rfl)
      | exact chiT_half_HP_zero m hm hm2 3 (Or.inr rfl) 2 (Or.inl rfl)
      | (exfalso; norm_num [weight] at hj)

/-- A quarter pair (orientation of `positivePairs`: `(c_s, i)`, `h_s = 1/4`). -/
def IsQuarterPair (m : ℕ) (p : Label m × Label m) : Prop :=
  ∃ (r : Fin (m - 1)) (i : Label m), p = (.inl r, i) ∧ weight m (.inl r) = 1 / 4 ∧
    r.val + 4 ≤ m ∧ 5 ≤ m ∧ weight m i = 9 / 4 ∧
    (∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r) ∧
    (∀ j : Label m, weight m j ≠ weight m (.inl r) + 1)

/-- The quarter pairs are discharged. -/
theorem pairSplitting_of_isQuarterPair (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (p : Label m × Label m) (hp : IsQuarterPair m p) : PairSplitting m hm p.1 p.2 := by
  obtain ⟨r, i, rfl, hw, hs, hm5, hwi, huq, hno1⟩ := hp
  have hq : hC m r = 1 / 4 := by simp only [hC]; rw [hw]; norm_num
  apply pairSplitting_swap m hm (by rw [hw, hwi]; norm_num)
  exact pairSplitting_quarter m hm hm2 r i hq hs hm5 (by rw [hwi, hw]; norm_num) huq hno1
    (fun j hj => chiT_ninefour_H4 m hm hm2 j (hj.trans hwi))

/-! ## The pairs of `m = 9, 10, 12` -/

theorem pairs_nine (hm : 1 ≤ 9) : ∀ p ∈ positivePairs 9, ¬ IsVacuumSignWeights 9 p →
    p.1 ≠ .inr 0 → PairSplitting 9 hm p.1 p.2 := by
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_nine_cert (i, j) hp with h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 9 hm (by decide +kernel)
      (pairSplitting_half_c3_nine hm 2 (Or.inl rfl))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 9 hm (by decide +kernel)
      (pairSplitting_half_c3_nine hm 3 (Or.inr rfl))

theorem pairs_ten (hm : 1 ≤ 10) : ∀ p ∈ positivePairs 10, ¬ IsVacuumSignWeights 10 p →
    p.1 ≠ .inr 0 → PairSplitting 10 hm p.1 p.2 := by
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_ten_cert (i, j) hp with h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 10 hm (by norm_num) 2 6 weight_ten_gap1
      weight_ten_c3 weight_ten_c7).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_c1_c9_ten hm

theorem pairs_twelve (hm : 1 ≤ 12) : ∀ p ∈ positivePairs 12, ¬ IsVacuumSignWeights 12 p →
    p.1 ≠ .inr 0 → PairSplitting 12 hm p.1 p.2 := by
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_twelve_cert (i, j) hp with h | h | h | h | h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 12 hm (by norm_num) 0 6 (by decide +kernel)
      (weight_twelve_uniq 0) (weight_twelve_uniq 6)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 12 hm (by norm_num) 3 7 (by decide +kernel)
      (weight_twelve_uniq 3) (weight_twelve_uniq 7)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_two_both 12 hm (by norm_num) 1 9 (by decide +kernel)
      (weight_twelve_uniq 1) (weight_twelve_uniq 9) weight_twelve_no1_c2
      (by rw [hC_twelve_c2]; norm_num) (by rw [hC_twelve_c2]; norm_num)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_two_both 12 hm (by norm_num) 4 10 (by decide +kernel)
      (weight_twelve_uniq 4) (weight_twelve_uniq 10) weight_twelve_no1_c5
      (by rw [hC_twelve_c5]; norm_num) (by rw [hC_twelve_c5]; norm_num)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 12 hm (by decide +kernel)
      (pairSplitting_half_sign_twelve hm 2 (Or.inl rfl))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_swap 12 hm (by decide +kernel)
      (pairSplitting_half_sign_twelve hm 3 (Or.inr rfl))

/-! ## The residual -/

/-- OPEN (true by Abe 2005, §7): the obligations not covered by `PlusRat3` and `PlusRat4`. -/
def RemainingAfterGapTwo : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → m ≠ 8 → m ≠ 9 → m ≠ 10 → m ≠ 12 → ∀ p ∈ positivePairs m,
    ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 → ¬ IsGapOneCharged m p → ¬ IsGapTwoCharged m p →
    ¬ IsQuarterPair m p → PairSplitting m hm p.1 p.2

/-- `RemainingAfterGapTwo → RemainingAfterGapOne`. -/
theorem remainingAfterGapOne_of_afterGapTwo (h : RemainingAfterGapTwo) : RemainingAfterGapOne := by
  intro m hm hm2 h8 p hp hvs hi hg1
  by_cases h9 : m = 9
  · subst h9; exact pairs_nine hm p hp hvs hi
  by_cases h10 : m = 10
  · subst h10; exact pairs_ten hm p hp hvs hi
  by_cases h12 : m = 12
  · subst h12; exact pairs_twelve hm p hp hvs hi
  by_cases hg2 : IsGapTwoCharged m p
  · exact pairSplitting_of_isGapTwoCharged m hm hm2 p hg2
  by_cases hq : IsQuarterPair m p
  · exact pairSplitting_of_isQuarterPair m hm hm2 p hq
  exact h m hm hm2 h8 h9 h10 h12 p hp hvs hi hg1 hg2 hq

/-- The residual implies rationality of every `V_{2m}⁺`, `m ≥ 2`. -/
theorem rationality_of_remainingAfterGapTwo (h : RemainingAfterGapTwo) : V2mPlusRationalFactGe2 :=
  rationality_of_remainingAfterGapOne (remainingAfterGapOne_of_afterGapTwo h)

end VOA.Classification.COne
