import VOA.DeligneAudit.D4CharPieriTranspose

/-! The coefficient recurrence of C(2,N), in every bidegree and every ambient rank. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Negative source degrees contribute zero by interlacing, not by a truncation hypothesis. -/
theorem gtCauchySlice_lower (q : R) (h : PochhammerUnits q) (N r s : ℕ)
    (lam : Fin (N + 2) → ℤ) (S : Finset (Fin (N + 2))) :
    (if S.card ≤ s then gtCauchySlice q h N r (s - S.card) (gtLowerSubset lam S)
      else 0) =
    if (∑ i, lam i) = (r + s : ℕ) then gtCauchyWeight q h r (gtLowerSubset lam S)
      else 0 := by
  by_cases hs : S.card ≤ s
  · rw [if_pos hs, gtCauchySlice_apply, gtLowerSubset_sum]
    have he : (∑ i, lam i) - (S.card : ℤ) = (r + (s - S.card) : ℕ) ↔
        (∑ i, lam i) = (r + s : ℕ) := by omega
    simp only [he]
  · rw [if_neg hs]
    split_ifs with hd
    · symm
      by_contra hn
      have hb := gtCauchyWeight_degree q h r (gtLowerSubset lam S) hn
      rw [gtLowerSubset_sum, hd] at hb
      omega
    · rfl

/-- X and B, summed on the finite free module of homogeneous rows. -/
theorem gtCauchySlice_shift_subsets (q : R) (h : PochhammerUnits q) (N r s : ℕ) :
    q ^ s • gtCauchySlice q h N r s =
      ∑ S : Finset (Fin (N + 2)), if S.card ≤ s then
        (-1 : R) ^ S.card • gtPieriUp q S (gtCauchySlice q h N r (s - S.card)) else 0 := by
  classical
  ext lam
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
  have ht (S : Finset (Fin (N + 2))) :
      (if S.card ≤ s then
        (-1 : R) ^ S.card • gtPieriUp q S (gtCauchySlice q h N r (s - S.card))
          else 0) lam =
        (-1 : R) ^ S.card *
          (if S.card ≤ s then gtCauchySlice q h N r (s - S.card) (gtLowerSubset lam S)
            else 0) * pieriCoeff q (gtLowerSubset lam S) S := by
    by_cases hs : S.card ≤ s <;>
      simp [hs, Finsupp.smul_apply, gtPieriUp_apply, mul_assoc]
  simp_rw [ht, gtCauchySlice_lower]
  rw [gtCauchySlice_apply]
  by_cases hd : (∑ i, lam i) = (r + s : ℕ)
  · simp only [if_pos hd]
    rw [gtCauchyWeight_subsets]
    have he : ((∑ i, lam i) - (r : ℤ)).toNat = s := by omega
    rw [he]
  · simp only [if_neg hd, mul_zero, zero_mul, Finset.sum_const_zero]

/-- Regroup finite subsets by cardinality, retaining only degrees at most s. -/
theorem gtSum_subsets_card {A : Type*} [AddCommMonoid A] (N s : ℕ)
    (f : ℕ → Finset (Fin N) → A) :
    (∑ j ∈ Finset.range (s + 1),
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, f j S) =
        ∑ S : Finset (Fin N), if S.card ≤ s then f S.card S else 0 := by
  classical
  have hu : (Finset.univ : Finset (Fin N)).powerset = Finset.univ := by ext; simp
  simp only [Finset.powersetCard_eq_filter, hu, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp [Finset.mem_range]

/-- The same recurrence grouped by elementary degree. -/
theorem gtCauchySlice_shift_card (q : R) (h : PochhammerUnits q) (N r s : ℕ) :
    q ^ s • gtCauchySlice q h N r s =
      ∑ j ∈ Finset.range (s + 1), (-1 : R) ^ j •
        ∑ S ∈ (Finset.univ : Finset (Fin (N + 2))).powersetCard j,
          gtPieriUp q S (gtCauchySlice q h N r (s - j)) := by
  simp_rw [Finset.smul_sum]
  rw [gtSum_subsets_card]
  exact gtCauchySlice_shift_subsets q h N r s

/-- The actual Cauchy coefficients satisfy the Euler-denominator recurrence. -/
theorem gtCauchyTwoCoeff_recurrence (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r s : ℕ) :
    q ^ s * gtCauchyTwoCoeff q h u N r s =
      ∑ j ∈ Finset.range (s + 1), (-1 : R) ^ j * pieriElementary u (N + 2) j *
        gtCauchyTwoCoeff q h u N r (s - j) := by
  have hh := congrArg (Finsupp.linearCombination R (gtEval q u (N + 2)))
    (gtCauchySlice_shift_card q h N r s)
  rw [map_smul, map_sum] at hh
  simp only [map_smul, smul_eq_mul, gtCauchySlice_eval] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro j _
  rw [gtPieriUp_eval_card q u j _ (gtCauchySlice_dominant q h N r (s - j)),
    gtCauchySlice_eval]
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_lower
#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_shift_subsets
#print axioms VOA.DeligneAudit.D4Char.gtSum_subsets_card
#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_shift_card
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwoCoeff_recurrence
