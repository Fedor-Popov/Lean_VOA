import VOA.Classification.COne.PlusSplitBottomValues
import VOA.Classification.COne.PlusSplitCharacterTable

/-! A computable, exact enumeration of positive integral character-table gaps.
Labels are retained even when their numerical lowest weights coincide.
Reference: Abe, https://arxiv.org/html/math/0311210#S7, Table 2. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.PlusResonantPairs
open PlusCharacterTable PlusSplitting
open VOA.Huang.LogRemovalAdmissible

/-- The omega column, in exact rational arithmetic. -/
def weight (m : ℕ) : Label m → ℚ
  | .inl r => ((r.val : ℚ) + 1)^2 / (4 * m)
  | .inr i => ![0, 1, (m : ℚ)/4, (m : ℚ)/4, 1/16, 9/16, 1/16, 9/16] i

theorem weight_eq_table (m : ℕ) (a : ℝ) (i : Label m) :
    (weight m i : ℝ) = (values m a i).1 := by
  rcases i with r | i
  · simp [weight, values]
  · fin_cases i <;> norm_num [weight, values, exceptional]

/-- Each pair is ordered (lower weight, higher weight). The denominator
test decides integrality; it does not compare floating-point approximations. -/
def positivePairs (m : ℕ) : Finset (Label m × Label m) :=
  Finset.univ.filter fun p =>
    0 < weight m p.2 - weight m p.1 ∧ (weight m p.2 - weight m p.1).den = 1

theorem mem_positivePairs_iff (m : ℕ) (i j : Label m) :
    (i, j) ∈ positivePairs m ↔
      ∃ z : ℤ, 0 < z ∧ (weight m j : ℂ) = (weight m i : ℂ) + (z : ℂ) := by
  simp only [positivePairs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpos, hden⟩
    have he := Rat.coe_int_num_of_den_eq_one hden
    refine ⟨(weight m j - weight m i).num, ?_, ?_⟩
    · have : (0 : ℚ) < ((weight m j - weight m i).num : ℚ) := by rwa [he]
      exact_mod_cast this
    · have hc := congrArg (fun q : ℚ => (q : ℂ)) he
      push_cast at hc
      linear_combination -hc
  · rintro ⟨z, hz, he⟩
    have hq : weight m j - weight m i = (z : ℚ) := by
      apply Rat.cast_injective (α := ℂ)
      push_cast
      linear_combination he
    rw [hq]
    exact ⟨by exact_mod_cast hz, Rat.den_intCast z⟩

/-- Both orientations of a nonzero integral gap are covered by the finite list. -/
theorem nonzero_gap_iff (m : ℕ) (i j : Label m) :
    (∃ z : ℤ, z ≠ 0 ∧ (weight m j : ℂ) = (weight m i : ℂ) + (z : ℂ)) ↔
      (i, j) ∈ positivePairs m ∨ (j, i) ∈ positivePairs m := by
  constructor
  · rintro ⟨z, hz, he⟩
    rcases lt_or_gt_of_ne hz with hn | hp
    · right
      apply (mem_positivePairs_iff m j i).mpr
      refine ⟨-z, by omega, ?_⟩
      push_cast
      linear_combination -he
    · exact Or.inl ((mem_positivePairs_iff m i j).mpr ⟨z, hp, he⟩)
  · rintro (hp | hp)
    · obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m i j).mp hp
      exact ⟨z, ne_of_gt hz, he⟩
    · obtain ⟨z, hz, he⟩ := (mem_positivePairs_iff m j i).mp hp
      refine ⟨-z, by omega, ?_⟩
      push_cast
      linear_combination -he

theorem lowestWeightValue_iff_label (m : ℕ) (hm : 1 ≤ m) (h : ℂ) :
    LowestWeightValue m h ↔ ∃ i : Label m, h = (weight m i : ℂ) := by
  constructor
  · rintro (rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩)
    · exact ⟨.inr 1, by norm_num [weight]⟩
    · exact ⟨.inr 4, by change (1 : ℂ)/16 = ((1/16 : ℚ) : ℂ); norm_num⟩
    · exact ⟨.inr 5, by change (9 : ℂ)/16 = ((9/16 : ℚ) : ℂ); norm_num⟩
    · refine ⟨.inr 2, ?_⟩
      change (m : ℂ)/4 = (Rat.cast ((m : ℚ)/4) : ℂ)
      push_cast
      rfl
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact ⟨.inr 0, by norm_num [weight]⟩
      · refine ⟨.inl ⟨j - 1, by omega⟩, ?_⟩
        have he : j - 1 + 1 = j := by omega
        simp only [weight, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
          Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
        have hc : ((j - 1 : ℕ) : ℂ) + 1 = (j : ℂ) := by exact_mod_cast he
        rw [hc]
  · rintro ⟨r | i, rfl⟩
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨r.val + 1, by have := r.isLt; omega, ?_⟩
      simp [weight]
    · fin_cases i <;> norm_num [weight, LowestWeightValue]
      exact Or.inr ⟨0, by omega, by simp⟩

/-- Table coverage for every intrinsic weak-subquotient bottom. -/
theorem label_of_factorBottom (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule (V2mPlus m hm) M)
    (a b : Submodule (modeAlg A) M) (hab : a ≤ b) (h : ℂ)
    (hb : FactorBottom A a b h) : ∃ i : Label m, h = (weight m i : ℂ) :=
  (lowestWeightValue_iff_label m hm h).mp
    (lowestWeightValue_of_factorBottom m hm hm2 A a b hab h hb)

theorem vacuum_sign_mem (m : ℕ) :
    (Sum.inr 0, Sum.inr 1) ∈ positivePairs m := by
  apply (mem_positivePairs_iff m _ _).mpr
  exact ⟨1, by norm_num, by norm_num [weight]⟩

/-- The half-lattice signs have equal bottoms, so are not a resonant pair. -/
theorem half_signs_not_mem (m : ℕ) :
    (Sum.inr 2, Sum.inr 3) ∉ positivePairs m := by
  simp [positivePairs, weight]

/-- No ordered pair among the four twisted labels has a positive integral gap. -/
theorem twisted_not_mem (m : ℕ) (i j : Fin 4) :
    (Sum.inr ⟨i.val + 4, by omega⟩, Sum.inr ⟨j.val + 4, by omega⟩)
      ∉ positivePairs m := by
  fin_cases i <;> fin_cases j <;> norm_num [positivePairs, weight]

/-- Reversing the factors negates, but does not remove, a nonzero integral gap. -/
theorem reverse_gap {h k : ℂ} {z : ℤ} (hz : z ≠ 0) (he : k = h + (z : ℂ)) :
    -z ≠ 0 ∧ h = k + ((-z : ℤ) : ℂ) := by
  refine ⟨neg_ne_zero.mpr hz, ?_⟩
  push_cast
  linear_combination -he

/-- For m=2 the finite list consists of exactly the vacuum/sign pair. -/
theorem positivePairs_two :
    positivePairs 2 = {(Sum.inr 0, Sum.inr 1)} := by
  ext ⟨i, j⟩
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> norm_num [positivePairs, weight]
  all_goals simp

/-- Resonance can involve a twisted and a charged row: 25/16 - 9/16 = 1.
The charged label has r.val=9, corresponding to charge r=10. -/
theorem twisted_charged_resonance :
    (Sum.inr 5, Sum.inl (9 : Fin 15)) ∈ positivePairs 16 := by
  norm_num [positivePairs, weight]
  change (9/16 : ℚ) < 25/16 ∧ ((25/16 : ℚ) - 9/16).den = 1
  norm_num

/-- Both half-lattice signs resonate with the vacuum when m=8. -/
theorem vacuum_half_resonance :
    (Sum.inr 0, Sum.inr 2) ∈ positivePairs 8 ∧
      (Sum.inr 0, Sum.inr 3) ∈ positivePairs 8 := by
  norm_num [positivePairs, weight]
  change (0 < (2 : ℚ) ∧ (2 : ℚ).den = 1) ∧
    (0 < (2 : ℚ) ∧ (2 : ℚ).den = 1)
  norm_num

end VOA.Classification.COne.PlusResonantPairs
