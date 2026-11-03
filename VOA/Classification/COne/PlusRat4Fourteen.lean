import VOA.Classification.COne.PlusRat4Gap3
import VOA.Classification.COne.PlusRat4Residual

/-! # `V₂₈⁺` (`m = 14`) and `V₃₀⁺` (`m = 15`) are strongly rational

Each has exactly one gap-three pair: `(c₁, c₁₃)` at `m = 14` (`h = 1/56`) and `(c₄, c₁₄)` at
`m = 15` (`h = 4/15`); the elimination certificates `gap3Cert_fourteen`, `gap3Cert_fifteen` are
checked here.  The remaining pairs are gap one and gap two.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4

theorem gap3Cert_fourteen : Gap3Cert (1 / 56) := by
  intro E _ _ V1 V2 V3 T2 T3 T4 A2 B2 A3 B3 C1 C2 C3 D1 D2 D3 hA2 hB2 hA3 hB3 e1 e2 e3 f1 f2 f3 R1 R2 R3
  have hA2' : A2 = 14 / 13 := by linear_combination (-14 / 13 : ℂ) * hA2
  have hB2' : B2 = -1 / 13 := by linear_combination (-14 / 13 : ℂ) * hB2
  have hA3' : A3 = 21 / 13 := by linear_combination (-14 / 13 : ℂ) * hA3
  have hB3' : B3 = -3 / 26 := by linear_combination (-14 / 13 : ℂ) * hB3
  subst hA2' hB2' hA3' hB3'
  have hC1 : C1 = 784/715 := by linear_combination (-4732/9075 : ℂ) * e1 + (-784/1815 : ℂ) * e2 + (3136/9075 : ℂ) * e3
  have hC2 : C2 = -56/715 := by linear_combination (6608/9075 : ℂ) * e1 + (532/605 : ℂ) * e2 + (-2128/3025 : ℂ) * e3
  have hC3 : C3 = -2/55 := by linear_combination (-6667/9075 : ℂ) * e1 + (-688/605 : ℂ) * e2 + (2147/3025 : ℂ) * e3
  have hD1 : D1 = 392/143 := by linear_combination (-4732/9075 : ℂ) * f1 + (-784/1815 : ℂ) * f2 + (3136/9075 : ℂ) * f3
  have hD2 : D2 = -28/143 := by linear_combination (6608/9075 : ℂ) * f1 + (532/605 : ℂ) * f2 + (-2128/3025 : ℂ) * f3
  have hD3 : D3 = -1/11 := by linear_combination (-6667/9075 : ℂ) * f1 + (-688/605 : ℂ) * f2 + (2147/3025 : ℂ) * f3
  subst hC1 hC2 hC3 hD1 hD2 hD3
  have key : (160221 / 1859 : ℂ) • (T2 - (784/715 : ℂ) • V1 - (-56/715 : ℂ) • V2 - (-2/55 : ℂ) • V3) = 0 := by
    linear_combination (norm := module) (879 / 286 : ℂ) • R1 + (-5 : ℂ) • R2 + (3 : ℂ) • R3
  exact (smul_eq_zero.mp key).resolve_left (by norm_num)

theorem gap3Cert_fifteen : Gap3Cert (4 / 15) := by
  intro E _ _ V1 V2 V3 T2 T3 T4 A2 B2 A3 B3 C1 C2 C3 D1 D2 D3 hA2 hB2 hA3 hB3 e1 e2 e3 f1 f2 f3 R1 R2 R3
  have hA2' : A2 = -15 := by linear_combination (15 : ℂ) * hA2
  have hB2' : B2 = 16 := by linear_combination (15 : ℂ) * hB2
  have hA3' : A3 = -45 / 2 := by linear_combination (15 : ℂ) * hA3
  have hB3' : B3 = 24 := by linear_combination (15 : ℂ) * hB3
  subst hA2' hB2' hA3' hB3'
  have hC1 : C1 = -225/11 := by linear_combination (-245/242 : ℂ) * e1 + (-375/484 : ℂ) * e2 + (75/121 : ℂ) * e3
  have hC2 : C2 = 240/11 := by linear_combination (270/121 : ℂ) * e1 + (475/242 : ℂ) * e2 + (-190/121 : ℂ) * e3
  have hC3 : C3 = -8/11 := by linear_combination (-306/121 : ℂ) * e1 + (-3593/1452 : ℂ) * e2 + (646/363 : ℂ) * e3
  have hD1 : D1 = -1125/22 := by linear_combination (-245/242 : ℂ) * f1 + (-375/484 : ℂ) * f2 + (75/121 : ℂ) * f3
  have hD2 : D2 = 600/11 := by linear_combination (270/121 : ℂ) * f1 + (475/242 : ℂ) * f2 + (-190/121 : ℂ) * f3
  have hD3 : D3 = -20/11 := by linear_combination (-306/121 : ℂ) * f1 + (-3593/1452 : ℂ) * f2 + (646/363 : ℂ) * f3
  subst hC1 hC2 hC3 hD1 hD2 hD3
  have key : (188559 / 11 : ℂ) • (T2 - (-225/11 : ℂ) • V1 - (240/11 : ℂ) • V2 - (-8/11 : ℂ) • V3) = 0 := by
    linear_combination (norm := module) (-2265 / 22 : ℂ) • R1 + (-5 : ℂ) • R2 + (3 : ℂ) • R3
  exact (smul_eq_zero.mp key).resolve_left (by norm_num)

end VOA.Classification.COne.PlusRat4

namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

theorem weight_uniq_fourteen (r : Fin 13) (j : Label 14) :
    weight 14 j = weight 14 (.inl r) → j = .inl r := by
  revert r j; decide +kernel

theorem weight_uniq_fifteen (r : Fin 14) (j : Label 15) :
    weight 15 j = weight 15 (.inl r) → j = .inl r := by
  revert r j; decide +kernel

theorem positivePairs_fourteen_cert : ∀ p ∈ positivePairs 14,
    ((weight 14 p.1 = 0 ∧ weight 14 p.2 = 1) ∨ (weight 14 p.1 = 1 ∧ weight 14 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 4, .inl 8) ∨ p = (.inl 2, .inl 10) ∨ p = (.inl 0, .inl 12) := by
  decide +kernel

theorem positivePairs_fifteen_cert : ∀ p ∈ positivePairs 15,
    ((weight 15 p.1 = 0 ∧ weight 15 p.2 = 1) ∨ (weight 15 p.1 = 1 ∧ weight 15 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 1, .inl 7) ∨ p = (.inl 6, .inl 12) ∨ p = (.inl 0, .inl 10) ∨
      p = (.inl 3, .inl 13) := by
  decide +kernel

theorem hC_14_0 : hC 14 0 = 1 / 56 := by norm_num [hC, weight]
theorem hC_14_2 : hC 14 2 = 9 / 56 := by norm_num [hC, weight]
theorem hC_15_6 : hC 15 6 = 49 / 60 := by norm_num [hC, weight]
theorem hC_15_0 : hC 15 0 = 1 / 60 := by norm_num [hC, weight]
theorem hC_15_3 : hC 15 3 = 4 / 15 := by norm_num [hC, weight]

/-- The gap-three pair of `m = 14`. -/
theorem pairSplitting_c1_c13_fourteen (hm : 1 ≤ 14) : PairSplitting 14 hm (.inl 0) (.inl 12) :=
  pairSplitting_swap 14 hm (by decide +kernel)
    (pairSplitting_charged_gap_three 14 hm (by norm_num) 0 12 (by decide +kernel)
      (weight_uniq_fourteen 0) (weight_uniq_fourteen 12) (by revert hm; decide +kernel)
      (by revert hm; decide +kernel) (by rw [hC_14_0]; norm_num) (by rw [hC_14_0]; norm_num)
      (by rw [hC_14_0]; exact gap3Cert_fourteen))

/-- The gap-three pair of `m = 15`. -/
theorem pairSplitting_c4_c14_fifteen (hm : 1 ≤ 15) : PairSplitting 15 hm (.inl 3) (.inl 13) :=
  pairSplitting_swap 15 hm (by decide +kernel)
    (pairSplitting_charged_gap_three 15 hm (by norm_num) 3 13 (by decide +kernel)
      (weight_uniq_fifteen 3) (weight_uniq_fifteen 13) (by revert hm; decide +kernel)
      (by revert hm; decide +kernel) (by rw [hC_15_3]; norm_num) (by rw [hC_15_3]; norm_num)
      (by rw [hC_15_3]; exact gap3Cert_fifteen))

theorem pairs_fourteen (hm : 1 ≤ 14) : ∀ p ∈ positivePairs 14, ¬ IsVacuumSignWeights 14 p →
    p.1 ≠ .inr 0 → PairSplitting 14 hm p.1 p.2 := by
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_fourteen_cert (i, j) hp with h | h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 14 hm (by norm_num) 4 8 (by decide +kernel)
      (weight_uniq_fourteen 4) (weight_uniq_fourteen 8)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_two_both 14 hm (by norm_num) 2 10 (by decide +kernel)
      (weight_uniq_fourteen 2) (weight_uniq_fourteen 10) (by revert hm; decide +kernel)
      (by rw [hC_14_2]; norm_num) (by rw [hC_14_2]; norm_num)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_c1_c13_fourteen hm

theorem pairs_fifteen (hm : 1 ≤ 15) : ∀ p ∈ positivePairs 15, ¬ IsVacuumSignWeights 15 p →
    p.1 ≠ .inr 0 → PairSplitting 15 hm p.1 p.2 := by
  rintro ⟨i, j⟩ hp hvs hi
  rcases positivePairs_fifteen_cert (i, j) hp with h | h | h | h | h | h
  · exact absurd h hvs
  · exact absurd h hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_one_both 15 hm (by norm_num) 1 7 (by decide +kernel)
      (weight_uniq_fifteen 1) (weight_uniq_fifteen 7)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_two_both 15 hm (by norm_num) 6 12 (by decide +kernel)
      (weight_uniq_fifteen 6) (weight_uniq_fifteen 12) (by revert hm; decide +kernel)
      (by rw [hC_15_6]; norm_num) (by rw [hC_15_6]; norm_num)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact (pairSplitting_charged_gap_two_both 15 hm (by norm_num) 0 10 (by decide +kernel)
      (weight_uniq_fifteen 0) (weight_uniq_fifteen 10) (by revert hm; decide +kernel)
      (by rw [hC_15_0]; norm_num) (by rw [hC_15_0]; norm_num)).2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact pairSplitting_c4_c14_fifteen hm

/-- **`V₂₈⁺ = V_{√28 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_fourteen (hm : 1 ≤ 14) : StronglyRational (V2mPlus 14 hm) :=
  V2mPlus_stronglyRational_of_unordered 14 hm (by norm_num) (pairs_fourteen hm)

/-- **`V₃₀⁺ = V_{√30 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_fifteen (hm : 1 ≤ 15) : StronglyRational (V2mPlus 15 hm) :=
  V2mPlus_stronglyRational_of_unordered 15 hm (by norm_num) (pairs_fifteen hm)

end VOA.Classification.COne

namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- OPEN (true by Abe 2005, §7): `RemainingAfterGapTwo` with `m = 14, 15` removed. -/
def RemainingAfterFifteen : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → m ≠ 8 → m ≠ 9 → m ≠ 10 → m ≠ 12 → m ≠ 14 → m ≠ 15 →
    ∀ p ∈ positivePairs m, ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 → ¬ IsGapOneCharged m p →
      ¬ IsGapTwoCharged m p → ¬ IsQuarterPair m p → PairSplitting m hm p.1 p.2

/-- `RemainingAfterFifteen → RemainingAfterGapTwo`. -/
theorem remainingAfterGapTwo_of_afterFifteen (h : RemainingAfterFifteen) : RemainingAfterGapTwo := by
  intro m hm hm2 h8 h9 h10 h12 p hp hvs hi hg1 hg2 hq
  by_cases h14 : m = 14
  · subst h14; exact pairs_fourteen hm p hp hvs hi
  by_cases h15 : m = 15
  · subst h15; exact pairs_fifteen hm p hp hvs hi
  exact h m hm hm2 h8 h9 h10 h12 h14 h15 p hp hvs hi hg1 hg2 hq

/-- The residual implies rationality of every `V_{2m}⁺`, `m ≥ 2`. -/
theorem rationality_of_remainingAfterFifteen (h : RemainingAfterFifteen) : V2mPlusRationalFactGe2 :=
  rationality_of_remainingAfterGapTwo (remainingAfterGapTwo_of_afterFifteen h)

end VOA.Classification.COne
