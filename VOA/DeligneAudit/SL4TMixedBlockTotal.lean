import VOA.DeligneAudit.SL4TMixedCellCount

/-! # The mixed-cell total over all valid parameter tuples -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Bounded coordinates containing every valid tuple at the given site counts. -/
abbrev MixedBoundedIndices (A B : ℕ) :=
  Fin (A + 1) × Fin (B + 1) × Fin (A + 1) × Fin (A + B + 1) × Fin (A + B + 1)

def mixedParamsOfIndices (A B : ℕ) (x : MixedBoundedIndices A B) : MixedParams :=
  ⟨A, B, x.1.val, x.2.1.val, x.2.2.1.val, x.2.2.2.1.val, x.2.2.2.2.val⟩

/-- All valid mixed parameter blocks at fixed numbers of a-sites and b-sites. -/
def mixedValidBlocks (A B : ℕ) : Finset MixedParams := by
  classical
  exact (Finset.univ.image (mixedParamsOfIndices A B)).filter MixedValid

theorem mem_mixedValidBlocks (A B : ℕ) (q : MixedParams) :
    q ∈ mixedValidBlocks A B ↔ MixedValid q ∧ q.A = A ∧ q.B = B := by
  classical
  constructor
  · intro h
    obtain ⟨hi, hv⟩ := Finset.mem_filter.mp h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hv, rfl, rfl⟩
  · rintro ⟨hv, hA, hB⟩
    have h := hv
    simp only [MixedValid, mixedP, mixedQ] at h
    let x : MixedBoundedIndices A B :=
      (⟨q.d1.toNat, by omega⟩, ⟨q.d2.toNat, by omega⟩, ⟨q.d3.toNat, by omega⟩,
        ⟨q.e1.toNat, by omega⟩, ⟨q.e2.toNat, by omega⟩)
    have he : mixedParamsOfIndices A B x = q := by
      dsimp [mixedParamsOfIndices, x]
      rw [Int.toNat_of_nonneg (show 0 ≤ q.d1 by omega),
        Int.toNat_of_nonneg (show 0 ≤ q.d2 by omega),
        Int.toNat_of_nonneg (show 0 ≤ q.d3 by omega),
        Int.toNat_of_nonneg (show 0 ≤ q.e1 by omega),
        Int.toNat_of_nonneg (show 0 ≤ q.e2 by omega), ← hA, ← hB]
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, he⟩, hv⟩

/-- The weighted cell count over all valid blocks is the product of the site weights. -/
theorem mixedBlockBound_sum_all_valid (A B : ℕ) :
    (∑ q ∈ mixedValidBlocks A B, mixedBlockBound q) = 15 ^ A * 6 ^ B := by
  rw [← mixedBlockBound_total A B]
  symm
  apply Finset.sum_subset
  · intro q hq
    exact (mem_mixedValidBlocks A B q).mpr (mixedRepresentedBlocks_valid A B q hq)
  · intro q hq hn
    obtain ⟨_, hA, hB⟩ := (mem_mixedValidBlocks A B q).mp hq
    exact mixedBlockBound_zero_of_unrepresented A B q hA hB hn

/-- Any ranks bounded block by block by the mixed cell bound satisfy the global site bound. -/
theorem mixedBlockRanks_sum_le (A B : ℕ) (rank : MixedParams → ℕ)
    (h : ∀ q ∈ mixedValidBlocks A B, rank q ≤ mixedBlockBound q) :
    (∑ q ∈ mixedValidBlocks A B, rank q) ≤ 15 ^ A * 6 ^ B := by
  rw [← mixedBlockBound_sum_all_valid A B]
  exact Finset.sum_le_sum h

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mem_mixedValidBlocks
#print axioms VOA.DeligneAudit.SL4T.mixedBlockBound_sum_all_valid
#print axioms VOA.DeligneAudit.SL4T.mixedBlockRanks_sum_le
