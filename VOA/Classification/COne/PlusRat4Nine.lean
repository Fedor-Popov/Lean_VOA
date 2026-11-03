import VOA.Classification.COne.PlusRat4Quarter
import VOA.Classification.COne.PlusRat4Ten

/-! # `V₁₈⁺` (`m = 9`) is strongly rational

The only remaining pairs at `m = 9` are `(c₃, half±)`: quotient `c₃` of weight `9/36 = 1/4`,
kernel a half row of weight `9/4`.  This is the degenerate case `h = 1/4` of the gap-two argument
(`pairSplitting_quarter`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

theorem positivePairs_nine_cert : ∀ p ∈ positivePairs 9,
    ((weight 9 p.1 = 0 ∧ weight 9 p.2 = 1) ∨ (weight 9 p.1 = 1 ∧ weight 9 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 2, .inr 2) ∨ p = (.inl 2, .inr 3) := by
  decide +kernel

theorem weight_nine_c3 (j : Label 9) : weight 9 j = weight 9 (.inl 2) → j = .inl 2 := by
  revert j; decide +kernel

theorem weight_nine_no1 (j : Label 9) : weight 9 j ≠ weight 9 (.inl 2) + 1 := by
  revert j; decide +kernel

theorem weight_nine_half (j : Label 9) : weight 9 j = 9 / 4 → j = .inr 2 ∨ j = .inr 3 := by
  revert j; decide +kernel

theorem hC_nine_c3 : hC 9 2 = 1 / 4 := by norm_num [hC, weight]

/-- The pairs (half kernel, `c₃` quotient) at `m = 9`. -/
theorem pairSplitting_half_c3_nine (hm : 1 ≤ 9) (i : Fin 8) (hi : i = 2 ∨ i = 3) :
    PairSplitting 9 hm (.inr i) (.inl 2) := by
  have hwi : weight 9 (.inr i) = 9 / 4 := by
    rcases hi with rfl | rfl
    · decide +kernel
    · decide +kernel
  apply pairSplitting_quarter 9 hm (by norm_num) 2 (.inr i) hC_nine_c3 (by norm_num) (by norm_num)
    (by rw [hwi]; decide +kernel) weight_nine_c3 weight_nine_no1
  intro j hj
  rw [hwi] at hj
  rcases weight_nine_half j hj with rfl | rfl
  · exact chiT_half_HP_zero 9 hm (by norm_num) 2 (Or.inl rfl) 2 (Or.inl rfl)
  · exact chiT_half_HP_zero 9 hm (by norm_num) 3 (Or.inr rfl) 2 (Or.inl rfl)

/-- **`V₁₈⁺ = V_{√18 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_nine (hm : 1 ≤ 9) : StronglyRational (V2mPlus 9 hm) := by
  apply V2mPlus_stronglyRational_of_unordered 9 hm (by norm_num)
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

end VOA.Classification.COne
