import VOA.Classification.COne.PlusRat4Charged
import VOA.Classification.COne.PlusRat3Residual

/-! # Gap-two charged pairs as a residual predicate, and `V₂₀⁺` (`m = 10`)

* `IsGapTwoCharged m p`: `p = (c_s, c_{s'})` with `s'² = s² + 8m`, both rows unique at their
  weights, no row of weight `h_s + 1`, `4h_s ≠ 1`, `64h_s ≠ 1`.
* `pairSplitting_of_isGapTwoCharged`: such pairs split (the orientation of `positivePairs`).
* `V2mPlus_stronglyRational_ten`: at `m = 10` the remaining pairs are the gap-one pair
  `(c₃, c₇)` and the gap-two pair `(c₁, c₉)`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- A gap-two charged/charged pair satisfying the hypotheses of the gap-two theorem. -/
def IsGapTwoCharged (m : ℕ) (p : Label m × Label m) : Prop :=
  ∃ r r' : Fin (m - 1), p = (.inl r, .inl r') ∧ weight m (.inl r') = weight m (.inl r) + 2 ∧
    (∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r) ∧
    (∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r') ∧
    (∀ j : Label m, weight m j ≠ weight m (.inl r) + 1) ∧
    4 * hC m r - 1 ≠ 0 ∧ 64 * hC m r - 1 ≠ 0

/-- Both orientations of a gap-two charged/charged pair. -/
theorem pairSplitting_charged_gap_two_both (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (r r' : Fin (m - 1))
    (hgap : weight m (.inl r') = weight m (.inl r) + 2)
    (huq : ∀ j : Label m, weight m j = weight m (.inl r) → j = .inl r)
    (huq' : ∀ j : Label m, weight m j = weight m (.inl r') → j = .inl r')
    (hno1 : ∀ j : Label m, weight m j ≠ weight m (.inl r) + 1)
    (h14 : 4 * hC m r - 1 ≠ 0) (h64 : 64 * hC m r - 1 ≠ 0) :
    PairSplitting m hm (.inl r') (.inl r) ∧ PairSplitting m hm (.inl r) (.inl r') :=
  ⟨pairSplitting_charged_gap_two m hm hm2 r r' hgap huq huq' hno1 h14 h64,
    pairSplitting_swap m hm (by rw [hgap]; intro h; linarith)
      (pairSplitting_charged_gap_two m hm hm2 r r' hgap huq huq' hno1 h14 h64)⟩

/-- The gap-two charged pairs are discharged. -/
theorem pairSplitting_of_isGapTwoCharged (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (p : Label m × Label m) (hp : IsGapTwoCharged m p) : PairSplitting m hm p.1 p.2 := by
  obtain ⟨r, r', rfl, hgap, huq, huq', hno1, h14, h64⟩ := hp
  exact (pairSplitting_charged_gap_two_both m hm hm2 r r' hgap huq huq' hno1 h14 h64).2

/-! ## `m = 10` -/

theorem positivePairs_ten_cert : ∀ p ∈ positivePairs 10,
    ((weight 10 p.1 = 0 ∧ weight 10 p.2 = 1) ∨ (weight 10 p.1 = 1 ∧ weight 10 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 2, .inl 6) ∨ p = (.inl 0, .inl 8) := by
  decide +kernel

theorem weight_ten_c3 (j : Label 10) : weight 10 j = weight 10 (.inl 2) → j = .inl 2 := by
  revert j; decide +kernel

theorem weight_ten_c7 (j : Label 10) : weight 10 j = weight 10 (.inl 6) → j = .inl 6 := by
  revert j; decide +kernel

theorem weight_ten_c1 (j : Label 10) : weight 10 j = weight 10 (.inl 0) → j = .inl 0 := by
  revert j; decide +kernel

theorem weight_ten_c9 (j : Label 10) : weight 10 j = weight 10 (.inl 8) → j = .inl 8 := by
  revert j; decide +kernel

theorem weight_ten_no1 (j : Label 10) : weight 10 j ≠ weight 10 (.inl 0) + 1 := by
  revert j; decide +kernel

theorem weight_ten_gap1 : weight 10 (.inl 6) = weight 10 (.inl 2) + 1 := by decide +kernel

theorem weight_ten_gap2 : weight 10 (.inl 8) = weight 10 (.inl 0) + 2 := by decide +kernel

theorem hC_ten_c1 : hC 10 0 = 1 / 40 := by norm_num [hC, weight]

/-- The gap-two pair of `m = 10`. -/
theorem pairSplitting_c1_c9_ten (hm : 1 ≤ 10) : PairSplitting 10 hm (.inl 0) (.inl 8) :=
  (pairSplitting_charged_gap_two_both 10 hm (by norm_num) 0 8 weight_ten_gap2 weight_ten_c1
    weight_ten_c9 weight_ten_no1 (by rw [hC_ten_c1]; norm_num) (by rw [hC_ten_c1]; norm_num)).2

/-- **`V₂₀⁺ = V_{√20 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_ten (hm : 1 ≤ 10) : StronglyRational (V2mPlus 10 hm) := by
  apply V2mPlus_stronglyRational_of_unordered 10 hm (by norm_num)
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_ten_cert (i, j) hp with h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 10 hm (by norm_num) 2 6 weight_ten_gap1
      weight_ten_c3 weight_ten_c7).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_c1_c9_ten hm

end VOA.Classification.COne
