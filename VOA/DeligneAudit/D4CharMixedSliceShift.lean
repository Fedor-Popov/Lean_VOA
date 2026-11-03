import VOA.DeligneAudit.D4CharMixedSlice

/-! The full homogeneous mixed shift on the finite free module of integer GL_5 rows. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtMixedSlice_lower (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ)
    (lam : Fin 5 → ℤ) (S : Finset (Fin 5)) :
    gtMixedSlice q h r (s - S.card) t v (gtLowerSubset lam S) =
      if (∑ i, lam i) = r + s - t - v then
        gtMixedWeight q h r t v (gtLowerSubset lam S) else 0 := by
  rw [gtMixedSlice_apply, gtLowerSubset_sum]
  have he : (∑ i, lam i) - (S.card : ℤ) = r + (s - S.card) - t - v ↔
      (∑ i, lam i) = r + s - t - v := by omega
  simp only [he]

theorem gtMixedSlice_qpow (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ)
    (lam : Fin 5 → ℤ) :
    q ^ s.toNat * gtMixedSlice q h r s t v lam =
      if (∑ i, lam i) = r + s - t - v then
        q ^ (lam 0 + lam 1 - r).toNat * gtMixedWeight q h r t v lam else 0 := by
  rw [gtMixedSlice_apply]
  split_ifs with hd
  · by_cases hn : gtMixedWeight q h r t v lam = 0
    · simp [hn]
    · have he := gtMixedWeight_sum q h r t v lam hn
      rw [show lam 0 + lam 1 - r = s by omega]
  · simp

/-- No formal infinite sum is used: the shift is an equality of finite row combinations. -/
theorem gtMixedSlice_shift_subsets (q : R) (h : PochhammerUnits q) (r : ℕ) (s t v : ℤ) :
    q ^ s.toNat • gtMixedSlice q h r s t v -
      q ^ (s - 1).toNat • gtMixedSlice q h r (s - 1) (t - 1) v -
      q ^ (s - 1).toNat • gtMixedSlice q h r (s - 1) t (v - 1) +
      q ^ (s - 2).toNat • gtMixedSlice q h r (s - 2) (t - 1) (v - 1) =
        ∑ S : Finset (Fin 5),
          (-1 : R) ^ S.card • gtPieriUp q S (gtMixedSlice q h r (s - S.card) t v) := by
  classical
  ext lam
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.finsetSum_apply, gtPieriUp_apply, gtMixedSlice_lower, gtMixedSlice_qpow]
  have h₁ : (r : ℤ) + (s - 1) - (t - 1) - v = r + s - t - v := by ring
  have h₂ : (r : ℤ) + (s - 1) - t - (v - 1) = r + s - t - v := by ring
  have h₃ : (r : ℤ) + (s - 2) - (t - 1) - (v - 1) = r + s - t - v := by ring
  simp only [h₁, h₂, h₃]
  by_cases hd : (∑ i, lam i) = r + s - t - v
  · simp only [if_pos hd]
    simp only [← mul_assoc]
    rw [gtMixedWeight_subsets]
    ring
  · simp [hd]

/-- Cardinality regrouping of the u-side, retaining precisely the possible x_2 degrees. -/
theorem gtMixedSlice_shift_card (q : R) (h : PochhammerUnits q) (r s : ℕ) (t v : ℤ) :
    q ^ s • gtMixedSlice q h r s t v -
      q ^ ((s : ℤ) - 1).toNat • gtMixedSlice q h r ((s : ℤ) - 1) (t - 1) v -
      q ^ ((s : ℤ) - 1).toNat • gtMixedSlice q h r ((s : ℤ) - 1) t (v - 1) +
      q ^ ((s : ℤ) - 2).toNat •
        gtMixedSlice q h r ((s : ℤ) - 2) (t - 1) (v - 1) =
      ∑ j ∈ Finset.range (s + 1), (-1 : R) ^ j •
        ∑ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard j,
          gtPieriUp q S (gtMixedSlice q h r (s - j : ℕ) t v) := by
  have hh := gtMixedSlice_shift_subsets q h r (s : ℤ) t v
  simp only [Int.toNat_natCast] at hh
  rw [hh]
  simp only [Finset.smul_sum]
  rw [gtSum_subsets_card]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hs : S.card ≤ s
  · rw [if_pos hs, Int.natCast_sub hs]
  · rw [if_neg hs, gtMixedSlice_zero q h r _ t v (by omega), map_zero, smul_zero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_lower
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_qpow
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_shift_subsets
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_shift_card
