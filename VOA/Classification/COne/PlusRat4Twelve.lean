import VOA.Classification.COne.PlusRat4Frame
import VOA.Classification.COne.PlusRat4SignModel
import VOA.Classification.COne.PlusRat4Ten

/-! # `V₂₄⁺` (`m = 12`) is strongly rational

Remaining pairs at `m = 12`: gap-one `(c₁, c₇)`, `(c₄, c₈)`; gap-two `(c₂, c₁₀)`, `(c₅, c₁₁)`
(`PlusRat4Charged`); and (sign, half±) with weights `1`, `3` (this file).

Sign quotient (`h = 1`, `o(H⁴) = o(H⁶) = 1`, `c₂ = 7/3`, `c₃ = 31/5`), half kernel
(`o(H⁴) = o(H⁶) = 0`): the `L(1), L(2)` equations give `w₂ = Q₂ - 2R`, `w₃ = Q₃ - 9R`; the
relations `r₁, r₂, r₃` combine as `6 r₃ - 10 r₂ + 30 r₁ = 153 (Q₂ - 2R)`; the `E`-eigenvalue is
`1242 ≠ 0`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

section Twelve
variable (hm : 1 ≤ 12)

@[reducible] local instance zhuRing12 : Ring (VOA.A (V2mPlus 12 hm)) := instRingA _
@[reducible] local instance zhuAlgebra12 : Algebra ℂ (VOA.A (V2mPlus 12 hm)) := instAlgebraA _

theorem two_le_twelve : 2 ≤ 12 := by norm_num

theorem weight_twelve_one (j : Label 12) : weight 12 j = 1 → j = .inr 1 := by
  revert j; decide +kernel

theorem weight_twelve_two (j : Label 12) : weight 12 j ≠ 2 := by
  revert j; decide +kernel

theorem weight_twelve_three (j : Label 12) : weight 12 j = 3 → j = .inr 2 ∨ j = .inr 3 := by
  revert j; decide +kernel

theorem uniq_twelve_one : ∀ j : Label 12, ((weight 12 j : ℚ) : ℂ) = (1 : ℂ) → j = .inr 1 := by
  intro j h
  apply weight_twelve_one
  have h' : ((weight 12 j : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by rw [h]; norm_num
  exact Rat.cast_injective h'

/-- **(half kernel, sign quotient) splits at `m = 12`**, for both half rows. -/
theorem pairSplitting_half_sign_twelve (i : Fin 8) (hi : i = 2 ∨ i = 3) :
    PairSplitting 12 hm (.inr i) (.inr 1) := by
  intro M _ _ A P hP hQ hb ht
  have hwi : ((weight 12 (.inr i) : ℚ) : ℂ) = 1 + 2 := by
    have h : weight 12 (.inr i) = 3 := by
      rcases hi with rfl | rfl
      · decide +kernel
      · decide +kernel
    rw [h]; norm_num
  have hw1 : ((weight 12 (.inr 1) : ℚ) : ℂ) = 1 := by norm_num [weight]
  rw [hwi] at hb
  rw [hw1] at ht
  have hlow := lowWeights 12 hm A hb ht
  obtain ⟨x, hxL, hxP, hx0, hxΩ⟩ := exists_top_lift 12 hm A hP hb ht
  -- the character of `x`
  set χ := chiT 12 hm two_le_twelve (.inr 1)
  have hχx := top_char_unique 12 hm two_le_twelve A hxΩ hxL (.inr 1) uniq_twelve_one
  have hzero : ∀ {k : ℤ} {a : VP 12 hm}, a ∈ (V2mPlus 12 hm).grading k →
      mode (A.YM a) (k - 1) x = χ (VOA.mk (V2mPlus 12 hm) a) • x := by
    intro k a ha
    have h1 := hχx (VOA.mk (V2mPlus 12 hm) a)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h1
    exact h1
  have hg2 := HP_mem_grading 12 hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading 12 hm 3 (by norm_num) (by norm_num)
  have h4 : mode (A.YM (HP 12 hm 2)) 3 x = (1 : ℂ) • x := by
    have h1 := hzero hg2
    rw [chiT_sign_HP 12 hm two_le_twelve 2 (Or.inl rfl)] at h1
    exact h1
  have h6 : mode (A.YM (HP 12 hm 3)) 5 x = (1 : ℂ) • x := by
    have h1 := hzero hg3
    rw [chiT_sign_HP 12 hm two_le_twelve 3 (Or.inr rfl)] at h1
    exact h1
  have hE0 : mode (A.YM (EP 12 hm)) (((12 : ℕ) : ℤ) - 1) x = 0 := by
    have h1 := hzero (EP_mem_grading 12 hm)
    have hv := (chiT_hasValues 12 hm two_le_twelve (.inr 1)).2.2
    change chiT 12 hm two_le_twelve (.inr 1) (VOA.mk (V2mPlus 12 hm) (EP 12 hm)) = _ at hv
    rw [hv] at h1
    simp [values, exceptional] at h1
    simpa using h1
  -- the sign model
  have heTD := sign_topData 12 hm two_le_twelve (by norm_num) uniq_twelve_one
  have he0 := signVector_ne_zero 12 hm
  -- degree one: the line
  have hD1 : Deg1Line A x := by
    intro j c hc
    have hte : mode ((signModule 12 hm).YM c) (j - 2) (signVector 12 hm) ∈ (signModule 12 hm).weight 2 := by
      have h := mode_mem_weight (signModule 12 hm) hc (signVector_mem 12 hm) (j - 2)
      have hc' : (1 : ℂ) + (j : ℂ) - ((j - 2 : ℤ) : ℂ) - 1 = 2 := by push_cast; ring
      rwa [hc'] at h
    obtain ⟨κ, hκ⟩ := sign_weight_two 12 hm (by norm_num) hte
    have hΩ := transfer_general A (signModule 12 hm).toWeakModule χ hxΩ heTD.omega hχx heTD.char
      he0 hxL hlow hc hκ
    refine ⟨κ, ?_⟩
    have hL : L0 A (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus 12 hm).conformalVector) 0 x) =
        (2 : ℂ) • (mode (A.YM c) (j - 2) x - κ • mode (A.YM (V2mPlus 12 hm).conformalVector) 0 x) := by
      rw [map_sub, map_smul, L0_mode_eigen A hxL hc, L0_mode_eigen A hxL (V2mPlus 12 hm).conformal_mem]
      push_cast
      module
    have h0 := top_eval_zero_of_rows 12 hm two_le_twelve A hΩ (c := 2) hL 1 (fun j hj => by
      exfalso; apply weight_twelve_two j
      apply Rat.cast_injective (α := ℂ)
      rw [hj]; norm_num)
    rw [topEvaluation_one] at h0
    exact sub_eq_zero.mp h0
  have hxTD : TopData A χ 1 x := ⟨hxΩ, hχx, hxL, hD1⟩
  have hLx0 := hxTD.Lm1_ne_zero one_ne_zero hx0
  -- the degree-one constants
  have coef1 : ∀ {j : ℤ} {c : VP 12 hm} {κ : ℂ} {β : ℂ}, c ∈ (V2mPlus 12 hm).grading j →
      mode (A.YM c) (j - 2) x = κ • mode (A.YM (V2mPlus 12 hm).conformalVector) 0 x →
      mode (A.YM (V2mPlus 12 hm).conformalVector) 2 (mode (A.YM c) (j - 2) x) = β • x →
      κ * (2 * 1) = β := by
    intro j c κ β _ hκ hβ
    rw [hκ, map_smul, L1_L A hxΩ hxL, smul_smul] at hβ
    have h1 : (κ * (2 * 1) - β) • x = 0 := by rw [sub_smul, hβ, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hx0)
  have hp2 : mode (A.YM (HP 12 hm 2)) 2 x = (7 / 3 : ℂ) • mode (A.YM (HP 12 hm 1)) 0 x := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ hg2
    rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num] at hκ
    have := coef1 hg2 (by rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num]; exact hκ)
      (by rw [show ((2 * 2 : ℕ) : ℤ) - 2 = 2 by norm_num]; exact L1G_p2 12 hm A hxΩ hxL h4)
    have hk : κ = 7 / 3 := by linear_combination this / 2
    rw [hκ, hk]; rfl
  have hp3 : mode (A.YM (HP 12 hm 3)) 4 x = (31 / 5 : ℂ) • mode (A.YM (HP 12 hm 1)) 0 x := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ hg3
    rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num] at hκ
    have := coef1 hg3 (by rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num]; exact hκ)
      (by rw [show ((2 * 3 : ℕ) : ℤ) - 2 = 4 by norm_num]; exact L1G_p3 12 hm A hxΩ hxL h4 h6)
    have hk : κ = 31 / 5 := by linear_combination this / 2
    rw [hκ, hk]; rfl
  have hE1 : mode (A.YM (EP 12 hm)) (((12 : ℕ) : ℤ) - 2) x = 0 := by
    obtain ⟨κ, hκ⟩ := hD1 _ _ (EP_mem_grading 12 hm)
    have := coef1 (β := 0) (EP_mem_grading 12 hm) hκ (by rw [L1G_v 12 hm A hxΩ hE0, zero_smul])
    have hk : κ = 0 := by linear_combination this / 2
    rw [hκ, hk, zero_smul]
  -- degree two: transfer
  have hTr : ∀ {k : ℤ} {t : VP 12 hm}, t ∈ (V2mPlus 12 hm).grading k →
      ∃ a b : ℂ, TopData.wv A x t k a b ∈ Omega A := by
    intro k t htk
    obtain ⟨a, b, hab⟩ := sign_deg2 12 hm two_le_twelve (by norm_num) htk
    refine ⟨a, b, transfer2 A (signModule 12 hm).toWeakModule χ hxTD heTD hx0 he0 one_ne_zero
      hlow htk ?_⟩
    simp only [TopData.wv]
    rw [hab]; abel
  -- the kernel character (half rows)
  have hker : ∀ w : M, w ∈ Omega A → L0 A w = ((1 : ℂ) + 2) • w →
      mode (A.YM (HP 12 hm 2)) 3 w = 0 ∧ mode (A.YM (HP 12 hm 3)) 5 w = 0 := by
    intro w hw hwL
    have hrow : ∀ t, t = 2 ∨ t = 3 →
        topEvaluation A w hw (VOA.mk (V2mPlus 12 hm) (HP 12 hm t)) = 0 :=
      fun t ht' => top_eval_zero_of_rows 12 hm two_le_twelve A hw (c := 1 + 2) hwL _ (fun j hj => by
        have hj3 : weight 12 j = 3 := by
          apply Rat.cast_injective (α := ℂ)
          rw [hj]; norm_num
        rcases weight_twelve_three j hj3 with rfl | rfl
        · exact chiT_half_HP_zero 12 hm two_le_twelve 2 (Or.inl rfl) t ht'
        · exact chiT_half_HP_zero 12 hm two_le_twelve 3 (Or.inr rfl) t ht')
    have e2 := hrow 2 (Or.inl rfl)
    have e3 := hrow 3 (Or.inr rfl)
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg2] at e2
    rw [topEvaluation_mk, oLevW_homogeneous A 0 hg3] at e3
    exact ⟨e2, e3⟩
  -- the quadratic sector
  obtain ⟨a2, b2, hw2⟩ := hTr hg2
  obtain ⟨a3, b3, hw3⟩ := hTr hg3
  simp only [TopData.wv] at hw2 hw3
  rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num] at hw2
  rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num] at hw3
  obtain ⟨⟨f1, f2⟩, ⟨f3, f4⟩, o4, o4', o6⟩ :=
    quad_relations 12 hm two_le_twelve A hxΩ hxL hx0 hLx0 h4 h6 hp2 hp3 hker hw2 hw3
  have hb2 : b2 = 0 := by linear_combination (2 / 3 : ℂ) * (f1 - f2)
  have ha2 : a2 = 2 := by linear_combination (-1 / 2 : ℂ) * f1 + (1 / 3 : ℂ) * f2
  have hb3 : b3 = 0 := by linear_combination (2 / 3 : ℂ) * (f3 - f4)
  have ha3 : a3 = 9 := by linear_combination (-1 / 2 : ℂ) * f3 + (1 / 3 : ℂ) * f4
  subst hb2 ha2 hb3 ha3
  have hrel : (153 : ℂ) • (mode (A.YM (HP 12 hm 2)) 1 x - (2 : ℂ) •
      mode (A.YM (V2mPlus 12 hm).conformalVector) 0 (mode (A.YM (V2mPlus 12 hm).conformalVector) 0 x)) = 0 := by
    linear_combination (norm := module) (6 : ℂ) • o6 - (10 : ℂ) • o4' + (30 : ℂ) • o4
  have hQ2mem : mode (A.YM (HP 12 hm 2)) 1 x ∈ RQspan 12 hm A x := by
    apply Submodule.mem_span_pair.mpr
    refine ⟨2, 0, ?_⟩
    have := (smul_eq_zero.mp hrel).resolve_left (by norm_num)
    rw [zero_smul, add_zero]
    exact (sub_eq_zero.mp this).symm
  -- the `E`-part
  have hv0 := E_deg2_zero 12 hm two_le_twelve A hxΩ hxL hx0 hLx0 (by norm_num) h4 hE0 hE1
    (fun w hw hwL => (hker w hw hwL).1) (hTr (EP_mem_grading 12 hm)) (by norm_num)
  -- conclusion
  have hST : ScalarTop A x := ⟨hxΩ, fun j c hc => ⟨_, hzero hc⟩⟩
  exact split_of_degTwo 12 hm two_le_twelve A P hP hQ hb ht hxΩ hxL hxP one_ne_zero (by norm_num)
    (degTwo_le 12 hm two_le_twelve A hST hD1 hQ2mem hv0)

end Twelve

end VOA.Classification.COne.PlusRat4

namespace VOA.Classification.COne
open PlusRat4 PlusRat3 PlusRat2 PlusResonantPairs PlusCharacterTable

theorem positivePairs_twelve_cert : ∀ p ∈ positivePairs 12,
    ((weight 12 p.1 = 0 ∧ weight 12 p.2 = 1) ∨ (weight 12 p.1 = 1 ∧ weight 12 p.2 = 0)) ∨
      p.1 = .inr 0 ∨ p = (.inl 0, .inl 6) ∨ p = (.inl 3, .inl 7) ∨ p = (.inl 1, .inl 9) ∨
      p = (.inl 4, .inl 10) ∨ p = (.inr 1, .inr 2) ∨ p = (.inr 1, .inr 3) := by
  decide +kernel

theorem weight_twelve_uniq (r : Fin 11) (j : Label 12) :
    weight 12 j = weight 12 (.inl r) → j = .inl r := by
  revert r j; decide +kernel

theorem weight_twelve_no1_c2 (j : Label 12) : weight 12 j ≠ weight 12 (.inl 1) + 1 := by
  revert j; decide +kernel

theorem weight_twelve_no1_c5 (j : Label 12) : weight 12 j ≠ weight 12 (.inl 4) + 1 := by
  revert j; decide +kernel

theorem hC_twelve_c2 : hC 12 1 = 1 / 12 := by norm_num [hC, weight]

theorem hC_twelve_c5 : hC 12 4 = 25 / 48 := by norm_num [hC, weight]

/-- **`V₂₄⁺ = V_{√24 ℤ}⁺` is strongly rational.** -/
theorem V2mPlus_stronglyRational_twelve (hm : 1 ≤ 12) : StronglyRational (V2mPlus 12 hm) := by
  apply V2mPlus_stronglyRational_of_unordered 12 hm (by norm_num)
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

end VOA.Classification.COne
