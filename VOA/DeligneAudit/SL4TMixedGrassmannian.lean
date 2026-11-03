import VOA.DeligneAudit.SL4TMixedSeries

/-! # Grassmannian tails and corner products in the mixed ring -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Inclusion of the three base alphabets among all five alphabets. -/
def mixedBaseIndex (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩

/-- The ambient size of each of the three base Grassmannians. -/
def mixedBaseSize (q : MixedParams) (i : Fin 3) : ℤ := ![q.A, q.B, q.A] i

/-- The size of each chosen base alphabet. -/
def mixedBaseLength (q : MixedParams) (i : Fin 3) : ℤ := ![q.d1, q.d2, q.d3] i

theorem mixedBase_valid (q : MixedParams) (hq : MixedValid q) (i : Fin 3) :
    0 ≤ mixedBaseLength q i ∧ mixedBaseLength q i ≤ mixedBaseSize q i := by
  fin_cases i <;> simp [mixedBaseLength, mixedBaseSize, MixedValid] at * <;> omega

theorem mixedBase_elementary_tail (q : MixedParams) (hq : MixedValid q) (i : Fin 3)
    (j : ℕ) (hj : (mixedBaseLength q i).toNat < j) :
    mixedEvaluation q (mixedE (mixedBaseIndex i) j) = 0 := by
  apply mixedRelation_zero q hq
  refine Or.inl ⟨mixedBaseIndex i, j, ?_, rfl⟩
  fin_cases i <;> simpa [mixedBaseLength, mixedBaseIndex, mixedLengths] using hj

/-- The original finite complete-function windows in the three base factors. -/
theorem mixedBase_complete_window (q : MixedParams) (hq : MixedValid q) (i : Fin 3)
    (j : ℕ) (hj : (mixedBaseSize q i - mixedBaseLength q i).toNat < j)
    (hu : j ≤ (mixedBaseSize q i).toNat) :
    mixedEvaluation q (mixedH (mixedBaseIndex i) j) = 0 := by
  apply mixedRelation_zero q hq
  fin_cases i
  · exact Or.inr (Or.inl ⟨j, hj, hu, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, hj, hu, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, hu, rfl⟩)))

/-- The finite defining windows imply every higher complete-function relation. -/
theorem mixedBase_complete_tail (q : MixedParams) (hq : MixedValid q) (i : Fin 3)
    (j : ℕ) (hj : (mixedBaseSize q i - mixedBaseLength q i).toNat < j) :
    mixedEvaluation q (mixedH (mixedBaseIndex i) j) = 0 := by
  have hv := mixedBase_valid q hq i
  have hsum : (mixedBaseSize q i - mixedBaseLength q i).toNat +
      (mixedBaseLength q i).toNat = (mixedBaseSize q i).toNat := by omega
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hu : j ≤ (mixedBaseSize q i).toNat
      · exact mixedBase_complete_window q hq i j hj hu
      · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
        simp only [mixedH, complete_succ, map_neg, map_sum, map_mul, map_pow, map_one]
        apply neg_eq_zero.mpr
        apply Finset.sum_eq_zero
        intro k _
        change _ * mixedEvaluation q (mixedE (mixedBaseIndex i) (k + 1)) *
          mixedEvaluation q (mixedH (mixedBaseIndex i) (n - k)) = 0
        by_cases he : (mixedBaseLength q i).toNat < k + 1
        · rw [mixedBase_elementary_tail q hq i (k + 1) he, mul_zero, zero_mul]
        · rw [ih (n - k) (by omega) (by omega), mul_zero]

/-- The elementary and complementary top classes multiply to zero at a positive-size site. -/
theorem mixedBase_corner_product (q : MixedParams) (hq : MixedValid q) (i : Fin 3)
    (hpos : 1 ≤ mixedBaseSize q i) :
    mixedEvaluation q (mixedE (mixedBaseIndex i) (mixedBaseLength q i).toNat) *
        mixedEvaluation q
          (mixedH (mixedBaseIndex i) (mixedBaseSize q i - mixedBaseLength q i).toNat) = 0 := by
  have hv := mixedBase_valid q hq i
  have heq : (mixedBaseSize q i).toNat - (mixedBaseLength q i).toNat =
      (mixedBaseSize q i - mixedBaseLength q i).toNat := by omega
  have h := congrArg ((mixedEvaluation q).comp (mixedAlphabet (mixedBaseIndex i)))
    (complete_relation (mixedBaseSize q i).toNat (by omega))
  simp only [AlgHom.comp_apply, map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at h
  change (∑ k ∈ Finset.range ((mixedBaseSize q i).toNat + 1),
    (-1) ^ k * mixedEvaluation q (mixedE (mixedBaseIndex i) k) *
      mixedEvaluation q (mixedH (mixedBaseIndex i) ((mixedBaseSize q i).toNat - k))) = 0
    at h
  rw [Finset.sum_eq_single (mixedBaseLength q i).toNat] at h
  · rw [heq, mul_assoc] at h
    exact (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow (mixedBaseLength q i).toNat)).mp h
  · intro k _ hne
    by_cases hd : (mixedBaseLength q i).toNat < k
    · rw [mixedBase_elementary_tail q hq i k hd, mul_zero, zero_mul]
    · rw [mixedBase_complete_tail q hq i _ (by omega), mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- The top of the first ambient alphabet is the product of its two base tops. -/
theorem mixedU_top (q : MixedParams) (hq : MixedValid q) :
    mixedEvaluation q (mixedU (mixedP q).toNat) =
      mixedEvaluation q (mixedE 0 q.d1.toNat) *
        ((-1) ^ (q.B - q.d2).toNat * mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat)) := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have hp : (mixedP q).toNat = q.d1.toNat + (q.B - q.d2).toNat := by
    simp only [mixedP]
    omega
  rw [hp]
  change mixedEvaluation q (mixedConv (mixedE 0) (fun j => (-1) ^ j * mixedH 1 j)
    (q.d1.toNat + (q.B - q.d2).toNat)) = _
  have h := mixedConv_top (mixedEvaluation q).toRingHom (mixedE 0)
    (fun j => (-1) ^ j * mixedH 1 j) q.d1.toNat (q.B - q.d2).toNat
    (fun j hj => mixedBase_elementary_tail q hq 0 j hj) (by
      intro j hj _
      simp only [map_mul, map_pow, map_neg, map_one]
      exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 1 j hj))
  simpa only [map_mul, map_pow, map_neg, map_one] using h

/-- The top of the second ambient alphabet is the product of its two base tops. -/
theorem mixedV_top (q : MixedParams) (hq : MixedValid q) :
    mixedEvaluation q (mixedV (mixedQ q).toNat) =
      mixedEvaluation q (mixedE 1 q.d2.toNat) *
        ((-1) ^ (q.A - q.d3).toNat * mixedEvaluation q (mixedH 2 (q.A - q.d3).toNat)) := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have hp : (mixedQ q).toNat = q.d2.toNat + (q.A - q.d3).toNat := by
    simp only [mixedQ]
    omega
  rw [hp]
  change mixedEvaluation q (mixedConv (mixedE 1) (fun j => (-1) ^ j * mixedH 2 j)
    (q.d2.toNat + (q.A - q.d3).toNat)) = _
  have h := mixedConv_top (mixedEvaluation q).toRingHom (mixedE 1)
    (fun j => (-1) ^ j * mixedH 2 j) q.d2.toNat (q.A - q.d3).toNat
    (fun j hj => mixedBase_elementary_tail q hq 1 j hj) (by
      intro j hj _
      simp only [map_mul, map_pow, map_neg, map_one]
      exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 2 j hj))
  simpa only [map_mul, map_pow, map_neg, map_one] using h

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedBase_valid
#print axioms VOA.DeligneAudit.SL4T.mixedBase_elementary_tail
#print axioms VOA.DeligneAudit.SL4T.mixedBase_complete_window
#print axioms VOA.DeligneAudit.SL4T.mixedBase_complete_tail
#print axioms VOA.DeligneAudit.SL4T.mixedBase_corner_product
#print axioms VOA.DeligneAudit.SL4T.mixedU_top
#print axioms VOA.DeligneAudit.SL4T.mixedV_top
