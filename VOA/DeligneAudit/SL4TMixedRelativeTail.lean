import VOA.DeligneAudit.SL4TMixedGrassmannian

/-! # Finite-window control of the relative alphabets in a mixed ring -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R : Type*} [CommRing R]

/-- A convolution vanishes beyond the sum of the two coefficient cutoffs. -/
theorem mixedConv_tail (φ : MixedPoly →+* R) (f g : ℕ → MixedPoly) (d w : ℕ)
    (hf : ∀ j, d < j → φ (f j) = 0) (hg : ∀ j, w < j → φ (g j) = 0)
    (n : ℕ) (hn : d + w < n) : φ (mixedConv f g n) = 0 := by
  simp only [mixedConv, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : d < i
  · rw [hf i hi, zero_mul]
  · rw [hg (n - i) (by omega), mul_zero]

/-- A monic inverse-series recursion extends a finite relative window to the full tail. -/
theorem mixedConv_relative_tail (φ : MixedPoly →+* R) (f g u : ℕ → MixedPoly)
    (d m : ℕ) (hd : d ≤ m) (hf0 : φ (f 0) = 1)
    (hconv : ∀ n, φ (mixedConv f g n) = φ (u n))
    (hf : ∀ j, d < j → φ (f j) = 0) (hu : ∀ j, m < j → φ (u j) = 0)
    (hw : ∀ j, m - d < j → j ≤ m → φ (g j) = 0)
    (n : ℕ) (hn : m - d < n) : φ (g n) = 0 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hnm : n ≤ m
      · exact hw n hn hnm
      · have h := hconv n
        rw [hu n (by omega)] at h
        simp only [mixedConv, map_sum, map_mul] at h
        rw [Finset.sum_eq_single 0] at h
        · simpa only [hf0, Nat.sub_zero, one_mul] using h
        · intro i hi hne
          by_cases hid : d < i
          · rw [hf i hid, zero_mul]
          · rw [ih (n - i) (by omega) (by omega), mul_zero]
        · intro hzero
          exact False.elim (hzero (Finset.mem_range.mpr (by omega)))

theorem mixedU_tail (q : MixedParams) (hq : MixedValid q) (n : ℕ)
    (hn : (mixedP q).toNat < n) : mixedEvaluation q (mixedU n) = 0 := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have heq : (mixedP q).toNat = q.d1.toNat + (q.B - q.d2).toNat := by
    simp only [mixedP]
    omega
  apply mixedConv_tail (mixedEvaluation q).toRingHom _ _ q.d1.toNat (q.B - q.d2).toNat
    (fun j hj => mixedBase_elementary_tail q hq 0 j hj) ?_ n (by omega)
  intro j hj
  simp only [map_mul, map_pow, map_neg, map_one]
  exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 1 j hj)

theorem mixedV_tail (q : MixedParams) (hq : MixedValid q) (n : ℕ)
    (hn : (mixedQ q).toNat < n) : mixedEvaluation q (mixedV n) = 0 := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have heq : (mixedQ q).toNat = q.d2.toNat + (q.A - q.d3).toNat := by
    simp only [mixedQ]
    omega
  apply mixedConv_tail (mixedEvaluation q).toRingHom _ _ q.d2.toNat (q.A - q.d3).toNat
    (fun j hj => mixedBase_elementary_tail q hq 1 j hj) ?_ n (by omega)
  intro j hj
  simp only [map_mul, map_pow, map_neg, map_one]
  exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 2 j hj)

/-- The first relative complement has precisely the required coefficient cutoff. -/
theorem mixedG1prime_tail (q : MixedParams) (hq : MixedValid q) (n : ℕ)
    (hn : (mixedP q - q.e1).toNat < n) :
    mixedEvaluation q (mixedG1prime n) = 0 := by
  have hv := hq
  simp only [MixedValid] at hv
  have heq : (mixedP q).toNat - q.e1.toNat = (mixedP q - q.e1).toNat := by omega
  apply mixedConv_relative_tail (mixedEvaluation q).toRingHom (mixedE 3) mixedG1prime
    mixedU q.e1.toNat (mixedP q).toNat (by omega) ?_ ?_ ?_
    (mixedU_tail q hq) ?_ n (by omega)
  · simp [mixedE]
  · intro j
    rw [mixedG1prime_convolution]
  · intro j hj
    exact mixedRelation_zero q hq _
      (Or.inl ⟨3, j, by simpa [mixedLengths] using hj, rfl⟩)
  · intro j hj hu
    exact mixedRelation_zero q hq _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, hu, rfl⟩)))))

/-- The second relative complement also satisfies its full tail relation. -/
theorem mixedG2prime_tail (q : MixedParams) (hq : MixedValid q) (n : ℕ)
    (hn : (mixedQ q - q.e2).toNat < n) :
    mixedEvaluation q (mixedG2prime n) = 0 := by
  have hv := hq
  simp only [MixedValid] at hv
  have heq : (mixedQ q).toNat - q.e2.toNat = (mixedQ q - q.e2).toNat := by omega
  apply mixedConv_relative_tail (mixedEvaluation q).toRingHom (mixedE 4) mixedG2prime
    mixedV q.e2.toNat (mixedQ q).toNat (by omega) ?_ ?_ ?_
    (mixedV_tail q hq) ?_ n (by omega)
  · simp [mixedE]
  · intro j
    rw [mixedG2prime_convolution]
  · intro j hj
    exact mixedRelation_zero q hq _
      (Or.inl ⟨4, j, by simpa [mixedLengths] using hj, rfl⟩)
  · intro j hj hu
    exact mixedRelation_zero q hq _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, hu, rfl⟩)))))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedConv_tail
#print axioms VOA.DeligneAudit.SL4T.mixedConv_relative_tail
#print axioms VOA.DeligneAudit.SL4T.mixedU_tail
#print axioms VOA.DeligneAudit.SL4T.mixedV_tail
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_tail
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_tail
