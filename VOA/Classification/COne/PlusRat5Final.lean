import VOA.Classification.COne.PlusRat5Main

/-! # Consequences of the uniform splitting theorem for `V_{2m}⁺`

* `pairSplitting_uniform`: a positive pair whose upper weight carries only charged/half rows
  and whose lower weight carries only charged/sign/half rows splits.
* `remainingUnordered_of_twistedKernel`: everything left of `RemainingUnordered` is the set of
  pairs whose lower weight is a twisted weight `1/16` or `9/16` (`TwistedKernelPairs`, OPEN).
* `V2mPlus_stronglyRational_of_not_four_dvd`: `V_{2m}⁺` is strongly rational for every `m ≥ 2`
  with `4 ∤ m` (unconditional).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3 PlusRat4 PlusRational

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)

/-- Charged or half row. -/
def IsCH (l : Label m) : Prop := (∃ r : Fin (m - 1), l = .inl r) ∨ l = .inr 2 ∨ l = .inr 3

/-- Untwisted, non-vacuum row. -/
def IsUT (l : Label m) : Prop := IsCH m l ∨ l = .inr 1

include hm in
theorem weight_CH (l : Label m) (hl : IsCH m l) :
    ∃ s' : ℕ, 1 ≤ s' ∧ s' ≤ m ∧ ((weight m l : ℚ) : ℂ) = ((((s' : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rcases hl with ⟨r, rfl⟩ | rfl | rfl
  · refine ⟨r.val + 1, by omega, by have := r.isLt; omega, ?_⟩
    simp [weight]
  · refine ⟨m, hm, le_rfl, ?_⟩
    simp [weight]; field_simp
  · refine ⟨m, hm, le_rfl, ?_⟩
    simp [weight]; field_simp

theorem weight_cast_inj {l l' : Label m} (h : ((weight m l : ℚ) : ℂ) = ((weight m l' : ℚ) : ℂ)) :
    weight m l = weight m l' := by exact_mod_cast h

include hm2 in
/-- **Uniform pair splitting.** -/
theorem pairSplitting_uniform (i j : Label m) (hp : (i, j) ∈ positivePairs m)
    (hU : ∀ l : Label m, weight m l = weight m j → IsCH m l)
    (hK : ∀ l : Label m, weight m l = weight m i → IsUT m l) :
    PairSplitting m (by omega) i j := by
  intro M _ _ A P hP hQ hb ht
  obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m i j).mp hp
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨s', hs'1, hs'm, hws'⟩ := weight_CH m hm1 j (hU j rfl)
  have hd : ((weight m j : ℚ) : ℂ) = ((weight m i : ℚ) : ℂ) + ((z.toNat : ℕ) : ℂ) := by
    rw [he]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hz.le).symm
  have hwre : ((weight m j : ℚ) : ℂ).re = (s' : ℝ) ^ 2 / (4 * m) := by
    rw [hws', Complex.ofReal_re]
  -- a kernel row has a different `s`
  have hdiff : ∀ jm : ℕ, ((weight m i : ℚ) : ℂ) = ((((jm : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ) → s' ≠ jm := by
    intro jm hjm hs
    subst hs
    rw [← hjm, he] at hws'
    have : ((z : ℂ)) = 0 := by linear_combination hws'
    have : z = 0 := by exact_mod_cast this
    omega
  apply split_uniform m hm1 hm2 A P hP hQ (h := ((weight m i : ℚ) : ℂ))
    (h' := ((weight m j : ℚ) : ℂ)) z.toNat (by omega) hd hb ht
  · intro l hl
    rcases hU l (weight_cast_inj m hl) with ⟨r, rfl⟩ | rfl | rfl
    · exact ⟨chiT_HP_zero m hm1 hm2 r 2 (Or.inl rfl), chiT_HP_zero m hm1 hm2 r 3 (Or.inr rfl)⟩
    · exact ⟨chiT_half_HP_zero m hm1 hm2 2 (Or.inl rfl) 2 (Or.inl rfl),
        chiT_half_HP_zero m hm1 hm2 2 (Or.inl rfl) 3 (Or.inr rfl)⟩
    · exact ⟨chiT_half_HP_zero m hm1 hm2 3 (Or.inr rfl) 2 (Or.inl rfl),
        chiT_half_HP_zero m hm1 hm2 3 (Or.inr rfl) 3 (Or.inr rfl)⟩
  · simp
  · intro n hn
    rw [hwre]
    have h1 : 4 * (m : ℝ) * ((s' : ℝ) ^ 2 / (4 * m)) = (s' : ℝ) ^ 2 := by field_simp
    rw [h1]
    have : (s' : ℝ) ≤ m := by exact_mod_cast hs'm
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) ≤ s' := by positivity
    nlinarith
  · intro l hl
    rcases hK l (weight_cast_inj m hl) with ((⟨r, rfl⟩ | rfl | rfl) | rfl)
    · apply modelSpec_charged m hm1 hm2 r
      intro N n hfib
      rw [hws'] at hfib
      refine fiber_pos m hm1 _ (by omega) (by have := r.isLt; omega) s' hs'1 hs'm ?_ hfib
      have hne := hdiff (r.val + 1) (by rw [← hl]; simp [weight])
      intro h0; apply hne; exact_mod_cast h0
    · apply modelSpec_half m hm1 hm2 2 (Or.inl rfl)
      intro N n hfib
      rw [hws'] at hfib
      refine fiber_pos m hm1 _ (by omega) le_rfl s' hs'1 hs'm ?_ hfib
      have hne := hdiff m (by rw [← hl]; simp [weight]; field_simp)
      intro h0; apply hne; exact_mod_cast h0
    · apply modelSpec_half m hm1 hm2 3 (Or.inr rfl)
      intro N n hfib
      rw [hws'] at hfib
      refine fiber_pos m hm1 _ (by omega) le_rfl s' hs'1 hs'm ?_ hfib
      have hne := hdiff m (by rw [← hl]; simp [weight]; field_simp)
      intro h0; apply hne; exact_mod_cast h0
    · apply modelSpec_sign m hm1 hm2
      · rw [hwre]
        have : (1 : ℝ) ≤ s' := by exact_mod_cast hs'1
        positivity
      · rw [hwre]
        have hs'R : (s' : ℝ) ≤ m := by exact_mod_cast hs'm
        rw [div_lt_iff₀ (by positivity)]
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        nlinarith

/-! ## The residual: twisted kernels -/

theorem weight_nonneg (l : Label m) : 0 ≤ weight m l := by
  rcases l with r | i
  · simp only [weight]; positivity
  · fin_cases i <;> simp [weight] <;> positivity

include hm in
theorem weight_eq_zero {l : Label m} (h : weight m l = 0) : l = .inr 0 := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  rcases l with r | i
  · exfalso
    simp only [weight] at h
    have h4 : (0 : ℚ) < 4 * m := by linarith
    have hr : (0 : ℚ) < ((r.val : ℚ) + 1) ^ 2 := by positivity
    have : (0 : ℚ) < ((r.val : ℚ) + 1) ^ 2 / (4 * m) := div_pos hr h4
    linarith
  · fin_cases i
    · rfl
    all_goals (exfalso; simp [weight] at h; try linarith)

theorem exceptional_weights (i : Fin 8) (h2 : i ≠ 2) (h3 : i ≠ 3) :
    weight m (.inr i) = 0 ∨ weight m (.inr i) = 1 ∨ weight m (.inr i) = 1 / 16 ∨
      weight m (.inr i) = 9 / 16 := by
  fin_cases i <;> simp_all [weight]

theorem exceptional_one (i : Fin 8) (h2 : i ≠ 2) (h3 : i ≠ 3) (h : weight m (.inr i) = 1) :
    i = 1 := by
  fin_cases i <;> simp_all [weight] <;> norm_num at h

theorem gap_pos {p : Label m × Label m} (hp : p ∈ positivePairs m) :
    ∃ z : ℤ, 1 ≤ z ∧ weight m p.2 = weight m p.1 + z := by
  obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m p.1 p.2).mp hp
  exact ⟨z, by omega, by exact_mod_cast he⟩

include hm hm2 in
/-- Every unordered obligation whose lower weight is not twisted splits. -/
theorem unordered_of_twisted
    (htw : ∀ p ∈ positivePairs m, (weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16) →
      PairSplitting m hm p.1 p.2) :
    ∀ p ∈ positivePairs m, ¬ IsVacuumSignWeights m p → p.1 ≠ .inr 0 →
      PairSplitting m hm p.1 p.2 := by
  intro p hp _ hp1 M _ _ A P
  have hm1 : 1 ≤ m := hm
  by_cases ht : weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16
  · exact htw p hp ht A P
  obtain ⟨z, hz, hgap⟩ := gap_pos m hp
  have hw1 : 0 ≤ weight m p.1 := weight_nonneg m p.1
  have hw1ne : weight m p.1 ≠ 0 := fun h0 => hp1 (weight_eq_zero m hm1 h0)
  have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz
  have hU : ∀ l : Label m, weight m l = weight m p.2 → IsCH m l := by
    intro l hl
    rw [hgap] at hl
    rcases l with r | i
    · exact Or.inl ⟨r, rfl⟩
    · by_cases h2 : i = 2
      · subst h2; exact Or.inr (Or.inl rfl)
      by_cases h3 : i = 3
      · subst h3; exact Or.inr (Or.inr rfl)
      exfalso
      rcases exceptional_weights m i h2 h3 with h | h | h | h <;> rw [h] at hl
      · linarith
      · -- weight one: then the lower weight is zero
        have h2' : weight m p.1 = 1 - z := by linarith
        have : z ≤ 1 := by
          have : (z : ℚ) ≤ 1 := by linarith
          exact_mod_cast this
        have hz' : z = 1 := by omega
        apply hw1ne; rw [h2', hz']; norm_num
      · linarith
      · linarith
  have hK : ∀ l : Label m, weight m l = weight m p.1 → IsUT m l := by
    intro l hl
    rcases l with r | i
    · exact Or.inl (Or.inl ⟨r, rfl⟩)
    · by_cases h1 : i = 1
      · subst h1; exact Or.inr rfl
      by_cases h2 : i = 2
      · subst h2; exact Or.inl (Or.inr (Or.inl rfl))
      by_cases h3 : i = 3
      · subst h3; exact Or.inl (Or.inr (Or.inr rfl))
      exfalso
      rcases exceptional_weights m i h2 h3 with h | h | h | h <;> rw [h] at hl
      · exact hw1ne hl.symm
      · exact h1 (exceptional_one m i h2 h3 h)
      · exact ht (Or.inl hl.symm)
      · exact ht (Or.inr hl.symm)
  exact pairSplitting_uniform m hm hm2 p.1 p.2 hp hU hK A P

end VOA.Classification.COne.PlusRat5

namespace VOA.Classification.COne
open PlusRat5 PlusRat2 PlusResonantPairs PlusCharacterTable

/-- OPEN (true by Abe 2005, §7): the obligations whose lower (kernel) weight is a twisted
weight `1/16` or `9/16`.  These are the only obligations not covered by `split_uniform`; they
occur only when `TwistArithFree m` fails (`noTwistedKernel_of_arith`), in particular only when
`4 ∣ m` (`noTwistedKernel_of_not_four_dvd`); for `m ≤ 100`: `m = 16, 36, 64, 68, 100`. -/
def TwistedKernelPairs : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ p ∈ positivePairs m,
    (weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16) → PairSplitting m hm p.1 p.2

/-- `TwistedKernelPairs → RemainingUnordered`. -/
theorem remainingUnordered_of_twistedKernel (h : TwistedKernelPairs) : RemainingUnordered := by
  intro m hm hm2 p hp hvs hp1
  exact unordered_of_twisted m hm hm2 (fun q hq htq => h m hm hm2 q hq htq) p hp hvs hp1

/-- **The residual implies rationality of every `V_{2m}⁺`, `m ≥ 2`.** -/
theorem rationality_of_twistedKernel (h : TwistedKernelPairs) : V2mPlusRationalFactGe2 :=
  rationality_of_remainingUnordered (remainingUnordered_of_twistedKernel h)

/-- `V_{2m}⁺` is strongly rational whenever no positive pair has a twisted lower weight. -/
theorem V2mPlus_stronglyRational_of_noTwistedKernel (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (h : ∀ p ∈ positivePairs m, ¬ (weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16)) :
    StronglyRational (V2mPlus m hm) :=
  V2mPlus_stronglyRational_of_unordered m hm hm2
    (unordered_of_twisted m hm hm2 (fun p hp htw => absurd htw (h p hp)))

end VOA.Classification.COne

namespace VOA.Classification.COne.PlusRat5
open PlusResonantPairs PlusCharacterTable

/-- The arithmetic condition excluding twisted lower weights: no charged row of weight
`c/16 + z` (`c ∈ {1,9}`, `z ≥ 1`), i.e. no `4s² = m(c + 16z)` with `s < m`. -/
def TwistArithFree (m : ℕ) : Prop :=
  ∀ s : ℕ, s < m → ∀ z : ℕ, 1 ≤ z → z ≤ m →
    4 * s ^ 2 ≠ m * (1 + 16 * z) ∧ 4 * s ^ 2 ≠ m * (9 + 16 * z)

instance (m : ℕ) : Decidable (TwistArithFree m) := by unfold TwistArithFree; infer_instance

/-- Under `TwistArithFree m` no positive pair has a twisted lower weight. -/
theorem noTwistedKernel_of_arith (m : ℕ) (hm2 : 2 ≤ m) (hA : TwistArithFree m) :
    ∀ p ∈ positivePairs m, ¬ (weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16) := by
  intro p hp htw
  obtain ⟨z, hz, hgap⟩ := gap_pos m hp
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨c, hc, hc1⟩ : ∃ c : ℤ, (c = 1 ∨ c = 9) ∧ weight m p.1 = (c : ℚ) / 16 := by
    rcases htw with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨9, Or.inr rfl, by rw [h]; norm_num⟩
  rw [hc1] at hgap
  rcases hq : p.2 with r | i
  · rw [hq] at hgap
    simp only [weight] at hgap
    have hZ : (4 * ((r.val : ℤ) + 1) ^ 2 : ℤ) = (m : ℤ) * (c + 16 * z) := by
      have : ((4 * ((r.val : ℤ) + 1) ^ 2 : ℤ) : ℚ) = (((m : ℤ) * (c + 16 * z) : ℤ) : ℚ) := by
        push_cast
        field_simp at hgap
        linarith
      exact_mod_cast this
    have hr := r.isLt
    obtain ⟨zn, rfl⟩ : ∃ zn : ℕ, z = (zn : ℤ) := ⟨z.toNat, by omega⟩
    have hzm : zn ≤ m := by
      have h1 : ((r.val : ℤ) + 1) ^ 2 < (m : ℤ) ^ 2 := by
        have : (r.val : ℤ) + 1 < m := by omega
        nlinarith
      have h2 : (m : ℤ) * (16 * zn) ≤ (m : ℤ) * (c + 16 * zn) := by
        have : (0 : ℤ) ≤ m := by positivity
        rcases hc with rfl | rfl <;> nlinarith
      by_contra hcon
      push Not at hcon
      have : (m : ℤ) < zn := by exact_mod_cast hcon
      nlinarith
    obtain ⟨hA1, hA9⟩ := hA (r.val + 1) (by omega) zn (by omega) hzm
    rcases hc with rfl | rfl
    · apply hA1; push_cast at hZ; exact_mod_cast hZ
    · apply hA9; push_cast at hZ; exact_mod_cast hZ
  · rw [hq] at hgap
    by_cases h2 : i = 2 ∨ i = 3
    · have hw : weight m (.inr i) = (m : ℚ) / 4 := by rcases h2 with rfl | rfl <;> simp [weight]
      rw [hw] at hgap
      have hZ : (4 * (m : ℤ) : ℤ) = c + 16 * z := by
        have : ((4 * (m : ℤ) : ℤ) : ℚ) = ((c + 16 * z : ℤ) : ℚ) := by push_cast; linarith
        exact_mod_cast this
      rcases hc with rfl | rfl <;> omega
    · push Not at h2
      rcases exceptional_weights m i h2.1 h2.2 with h | h | h | h <;> rw [h] at hgap
      · have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz
        rcases hc with rfl | rfl <;> norm_num at hgap <;> linarith
      · have : ((16 : ℤ) : ℚ) = ((c + 16 * z : ℤ) : ℚ) := by push_cast; linarith
        have : (16 : ℤ) = c + 16 * z := by exact_mod_cast this
        rcases hc with rfl | rfl <;> omega
      · have : ((1 : ℤ) : ℚ) = ((c + 16 * z : ℤ) : ℚ) := by push_cast; linarith
        have : (1 : ℤ) = c + 16 * z := by exact_mod_cast this
        rcases hc with rfl | rfl <;> omega
      · have : ((9 : ℤ) : ℚ) = ((c + 16 * z : ℤ) : ℚ) := by push_cast; linarith
        have : (9 : ℤ) = c + 16 * z := by exact_mod_cast this
        rcases hc with rfl | rfl <;> omega

/-- `4 ∤ m ⇒ TwistArithFree m`. -/
theorem twistArithFree_of_not_four_dvd (m : ℕ) (h4 : ¬ 4 ∣ m) : TwistArithFree m := by
  intro s _ z _ _
  constructor
  · intro h; apply h4
    exact ⟨s ^ 2 - 4 * m * z, by
      have : (m : ℤ) = 4 * ((s : ℤ) ^ 2 - 4 * m * z) := by
        have : ((4 * s ^ 2 : ℕ) : ℤ) = ((m * (1 + 16 * z) : ℕ) : ℤ) := by rw [h]
        push_cast at this; linarith
      omega⟩
  · intro h; apply h4
    refine ⟨s ^ 2 - 4 * m * z - 2 * m, ?_⟩
    have : (m : ℤ) = 4 * ((s : ℤ) ^ 2 - 4 * m * z - 2 * m) := by
      have : ((4 * s ^ 2 : ℕ) : ℤ) = ((m * (9 + 16 * z) : ℕ) : ℤ) := by rw [h]
      push_cast at this; linarith
    omega

theorem noTwistedKernel_of_not_four_dvd (m : ℕ) (hm2 : 2 ≤ m) (h4 : ¬ 4 ∣ m) :
    ∀ p ∈ positivePairs m, ¬ (weight m p.1 = 1 / 16 ∨ weight m p.1 = 9 / 16) :=
  noTwistedKernel_of_arith m hm2 (twistArithFree_of_not_four_dvd m h4)

end VOA.Classification.COne.PlusRat5

namespace VOA.Classification.COne
open PlusRat5

/-- **`V_{2m}⁺` is strongly rational for every `m ≥ 2` with `4 ∤ m`** (unconditional). -/
theorem V2mPlus_stronglyRational_of_not_four_dvd (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (h4 : ¬ 4 ∣ m) : StronglyRational (V2mPlus m hm) :=
  V2mPlus_stronglyRational_of_noTwistedKernel m hm hm2 (noTwistedKernel_of_not_four_dvd m hm2 h4)

end VOA.Classification.COne

namespace VOA.Classification.COne
open PlusRat5

/-- **`V_{2m}⁺` is strongly rational whenever `TwistArithFree m`** (unconditional; decidable
per `m`; fails for `m ≤ 400` exactly at `m = 16, 36, 64, 68, 100, 132, 144, 164, 196, 228, 256,
260, 272, 292, 324, 356, 388, 400` by `twisted.py`). -/
theorem V2mPlus_stronglyRational_of_twistArithFree (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (hA : TwistArithFree m) : StronglyRational (V2mPlus m hm) :=
  V2mPlus_stronglyRational_of_noTwistedKernel m hm hm2 (noTwistedKernel_of_arith m hm2 hA)

end VOA.Classification.COne
