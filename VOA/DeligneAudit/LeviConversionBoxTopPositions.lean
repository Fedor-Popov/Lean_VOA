import VOA.DeligneAudit.LeviConversionBox

/-! Positional subset facts for the universal top Wick contraction. -/

namespace VOA.DeligneAudit.LeviConversion

open Finset

/-- Positions carrying a zero mode, including any appended zero letters. -/
def zeroPositions {n : ℕ} (x : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = 0

/-- Exactly the expected number of size-`k` positional choices use only zeros. -/
theorem zero_contraction_count {n k : ℕ} (x : Fin n → ℕ) :
    ((zeroPositions x).powersetCard k).card =
      Nat.choose (zeroPositions x).card k := by
  exact Finset.card_powersetCard k (zeroPositions x)

/-- The zero-position count for the original modes and the `k` appended zeros. -/
theorem appended_zero_positions_card (xs : List ℕ) (k : ℕ) :
    (zeroPositions (fun i : Fin (xs ++ List.replicate k 0).length =>
      (xs ++ List.replicate k 0).get i)).card = xs.count 0 + k := by
  let v : List.Vector ℕ (xs ++ List.replicate k 0).length :=
    ⟨xs ++ List.replicate k 0, rfl⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count 0 v
  change (zeroPositions (fun i : Fin (xs ++ List.replicate k 0).length =>
    (xs ++ List.replicate k 0).get i)).card =
      (xs ++ List.replicate k 0).count 0 at h
  simpa [List.count_append] using h

/-- Any other positional choice contracts a strictly positive mode. -/
theorem nonzero_contraction {n k : ℕ} (x : Fin n → ℕ)
    (T : Finset (Fin n)) (_hT : T ∈ (Finset.univ : Finset (Fin n)).powersetCard k)
    (hnot : ¬ T ⊆ zeroPositions x) :
    ∃ i ∈ T, 0 < x i := by
  obtain ⟨i, hi, hiz⟩ := Finset.not_subset.mp hnot
  refine ⟨i, hi, ?_⟩
  have hx : x i ≠ 0 := by
    intro h
    apply hiz
    simp [zeroPositions, h]
  omega

/-- Removing the contracted positions strictly lowers the uncontracted
mode sum whenever a nonzero mode is contracted. -/
theorem nonzero_contraction_lowers_sum {n k : ℕ} (x : Fin n → ℕ)
    (T : Finset (Fin n))
    (hT : T ∈ (Finset.univ : Finset (Fin n)).powersetCard k)
    (hnot : ¬ T ⊆ zeroPositions x) :
    ∑ i ∈ (Finset.univ : Finset (Fin n)) \ T, x i < ∑ i, x i := by
  obtain ⟨i, hi, hpos⟩ := nonzero_contraction x T hT hnot
  apply Finset.sum_lt_sum_of_subset
  · exact Finset.sdiff_subset
  · exact Finset.mem_univ i
  · simpa using hi
  · exact hpos
  · intro j hj _
    exact Nat.zero_le _

/-- The strict decrease is measured against the original modes, since the
appended modes contribute zero. -/
theorem appended_nonzero_lowers_original (xs : List ℕ) (k : ℕ)
    (T : Finset (Fin (xs ++ List.replicate k 0).length))
    (hT : T ∈ (Finset.univ : Finset (Fin (xs ++ List.replicate k 0).length)).powersetCard k)
    (hnot : ¬ T ⊆ zeroPositions
      (fun i : Fin (xs ++ List.replicate k 0).length =>
        (xs ++ List.replicate k 0).get i)) :
    ∑ i ∈ (Finset.univ : Finset (Fin (xs ++ List.replicate k 0).length)) \ T,
      (xs ++ List.replicate k 0).get i < xs.sum := by
  have h := nonzero_contraction_lowers_sum
    (fun i : Fin (xs ++ List.replicate k 0).length =>
      (xs ++ List.replicate k 0).get i) T hT hnot
  simpa only [← List.sum_ofFn, List.ofFn_get, List.sum_append,
    List.sum_replicate, mul_zero, add_zero] using h

end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.zero_contraction_count
#print axioms VOA.DeligneAudit.LeviConversion.appended_zero_positions_card
#print axioms VOA.DeligneAudit.LeviConversion.nonzero_contraction
#print axioms VOA.DeligneAudit.LeviConversion.nonzero_contraction_lowers_sum
#print axioms VOA.DeligneAudit.LeviConversion.appended_nonzero_lowers_original
