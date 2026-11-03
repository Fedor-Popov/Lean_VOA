import VOA.DeligneAudit.SL4TThomRelations

/-! # Vanishing Thom pieces at the boundary of the index rectangle -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

theorem hClass_height_zero (T j : ℕ) (hj : 0 < j) : hClass 0 T j = 0 := by
  have h := grass_convolution 0 T j hj
  rw [Finset.sum_eq_single 0] at h
  · simpa only [pow_zero, eClass, elementary_zero, map_one, one_mul, Nat.sub_zero] using h
  · intro i _ hi
    rw [eClass_eq_zero 0 T i (by omega), mul_zero, zero_mul]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem leftE_zero_index (M a b : ℕ) : leftE M a b 0 = 1 := by
  simp only [leftE, eClass, elementary_zero, map_one]

theorem rightE_zero_index (M a b : ℕ) : rightE M a b 0 = 1 := by
  simp only [rightE, eClass, elementary_zero, map_one]

theorem leftH_zero_index (M a b : ℕ) : leftH M a b 0 = 1 := by
  simp only [leftH, hClass, complete_zero, map_one]

theorem rightH_zero_index (M a b : ℕ) : rightH M a b 0 = 1 := by
  simp only [rightH, hClass, complete_zero, map_one]

theorem eClass_eq_zero_of_width_zero (d T j : ℕ) (hT : T = 0) (hj : 0 < j) :
    eClass d T j = 0 := by
  subst T
  exact eClass_width_zero d j hj

theorem leftE_top (M b : ℕ) (hM : 0 < M) : leftE M M b M = 0 := by
  unfold leftE
  rw [eClass_eq_zero_of_width_zero M (M - M) M (Nat.sub_self M) hM, map_zero]

theorem rightE_top (M a : ℕ) (hM : 0 < M) : rightE M a M M = 0 := by
  unfold rightE
  rw [eClass_eq_zero_of_width_zero M (M - M) M (Nat.sub_self M) hM, map_zero]

theorem leftH_empty (M b : ℕ) (hM : 0 < M) : leftH M 0 b M = 0 := by
  unfold leftH
  rw [hClass_height_zero _ _ hM, map_zero]

theorem rightH_empty (M a : ℕ) (hM : 0 < M) : rightH M a 0 M = 0 := by
  unfold rightH
  rw [hClass_height_zero _ _ hM, map_zero]

theorem thomI1_top_left (M b : ℕ) (hM : 0 < M) : thomI1 M M b = ⊥ := by
  simp only [thomI1, leftE_top M b hM, zero_mul, Ideal.span_singleton_zero]

theorem thomI1_top_right (M a : ℕ) (hM : 0 < M) : thomI1 M a M = ⊥ := by
  simp only [thomI1, rightE_top M a hM, mul_zero, Ideal.span_singleton_zero]

theorem thomI1_zero_right (M a : ℕ) : thomI1 M a 0 = thomI2 M a 0 := by
  simp only [thomI1, rightE_zero_index, mul_one, thomI2]

theorem thomI2_zero_left (M b : ℕ) : thomI2 M 0 b = ⊤ := by
  simp only [thomI2, leftE_zero_index, Ideal.span_singleton_one]

theorem thomNGPiece_top_left (M b : ℕ) (hM : 0 < M) : ThomNGPiece M M b = ⊥ := by
  simp only [ThomNGPiece, leftE_top M b hM, map_zero, Ideal.span_singleton_zero]

theorem thomNGPiece_zero_right (M a : ℕ) : ThomNGPiece M a 0 = ⊥ := by
  have h : Ideal.Quotient.mk (thomI1 M a 0) (leftE M a 0 a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [thomI1_zero_right]
    exact Ideal.subset_span (Set.mem_singleton _)
  simp only [ThomNGPiece, h, Ideal.span_singleton_zero]

theorem thomBothPiece_zero_left (M b : ℕ) : ThomBothPiece M 0 b = ⊥ := by
  have h : Ideal.Quotient.mk (thomI2 M 0 b) (rightH M 0 b (M - b)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [thomI2_zero_left]
    trivial
  simp only [ThomBothPiece, h, Ideal.span_singleton_zero]

theorem thomBothPiece_zero_right (M a : ℕ) (hM : 0 < M) : ThomBothPiece M a 0 = ⊥ := by
  simp only [ThomBothPiece, Nat.sub_zero, rightH_empty M a hM, map_zero,
    Ideal.span_singleton_zero]

theorem thomI3_zero_left (M b : ℕ) : thomI3 M 0 b = ⊤ := by
  rw [thomI3, thomI2_zero_left, top_sup_eq]

theorem thomI3_top_right (M a : ℕ) : thomI3 M a M = ⊤ := by
  have h : rightH M a M (M - M) = 1 :=
    (congrArg (rightH M a M) (Nat.sub_self M)).trans (rightH_zero_index M a M)
  rw [thomI3, h, Ideal.span_singleton_one, sup_top_eq]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.hClass_height_zero
#print axioms VOA.DeligneAudit.SL4T.thomI1_top_left
#print axioms VOA.DeligneAudit.SL4T.thomI1_top_right
#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_top_left
#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_zero_right
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_zero_left
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_zero_right
#print axioms VOA.DeligneAudit.SL4T.thomI3_zero_left
#print axioms VOA.DeligneAudit.SL4T.thomI3_top_right
