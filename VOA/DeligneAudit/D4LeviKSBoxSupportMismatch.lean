import VOA.DeligneAudit.D4LeviKSFlagDegenerate

/-! The current box-count support excludes some nonempty rectangles. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.A3Sector

theorem ksZeroOccupation_mem_box (q n : ℕ) (hn : n ≤ q) :
    Finsupp.single 0 n ∈ a2BoxModeSet q n := by
  rw [mem_a2BoxModeSet q n hn]
  constructor
  · simp
  · intro r hr
    have hr0 : r = 0 := by
      by_contra hne
      simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne, Ne.symm hne] at hr
    subst r
    simpa using hn

/-- Every non-overfull triple has at least its all-zero box word. -/
theorem ksGradedBoxCount_zero_pos (m a b c : ℕ) (h : a + b + c ≤ m) :
    0 < ksGradedBoxCount m a b c 0 := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨((Finsupp.single 0 a, Finsupp.single 0 b), Finsupp.single 0 c), ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨ksZeroOccupation_mem_box _ _ (by omega),
          ksZeroOccupation_mem_box _ _ (by omega)⟩,
        ksZeroOccupation_mem_box _ _ (by omega)⟩
  · simp [ksBoxDegree, Finsupp.weight_single, om]

/-- This is precisely the extra `a ≤ b₊` cutoff in the current definition. -/
theorem ksBoxCount_zero_of_unpaired_gt_complement (m a b c d : ℕ)
    (ha : m - (a + b) - c < a) :
    ksBoxCount m (pairFinalKey a b c d) = 0 := by
  apply if_neg
  simp only [pairFinalKey]
  omega

/-- The existing supported-key count disagrees with its actual mode-box count
    throughout the nonempty range `0 ≤ b₊ < a`. -/
theorem ksBoxCount_ne_graded_of_unpaired_gt_complement (m a b c : ℕ)
    (h : a + b + c ≤ m) (ha : m - (a + b) - c < a) :
    ksBoxCount m (pairFinalKey a b c 0) ≠ ksGradedBoxCount m a b c 0 := by
  rw [ksBoxCount_zero_of_unpaired_gt_complement m a b c 0 ha]
  exact Nat.ne_of_lt (ksGradedBoxCount_zero_pos m a b c h)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksZeroOccupation_mem_box
#print axioms VOA.DeligneAudit.D4Levi.ksGradedBoxCount_zero_pos
#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_zero_of_unpaired_gt_complement
#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_ne_graded_of_unpaired_gt_complement
