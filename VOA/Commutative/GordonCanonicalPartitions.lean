/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonResidualFiltration

/-! # Canonical descending block evaluations indexed by actual partitions -/

namespace VOA.GordonCanonicalPartitions

open VOA.GordonFiltration VOA.GordonBlockEquiv VOA.GordonPartitionOrder

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The paper's partition written as a descending composition. -/
def descendingComposition {n : ℕ} (lam : Nat.Partition n) : Composition n where
  blocks := lam.parts.sort (· ≥ ·)
  blocks_pos := by intro i hi; exact lam.parts_pos (by simpa using hi)
  blocks_sum := by
    rw [← Multiset.sum_coe, Multiset.sort_eq]
    exact lam.parts_sum

/-- The literal cardinality of a composition block. -/
theorem blockSize_composition_index {n : ℕ} (c : Composition n) (i : Fin c.length) :
    blockSize c.index i = c.blocksFun i := by
  rw [blockSize_eq_card_fiber]
  have he : Fin (c.blocksFun i) ≃ {j : Fin n // c.index j = i} :=
    Equiv.ofBijective (fun j ↦ ⟨c.embedding i j, c.index_embedding i j⟩) (by
      constructor
      · intro j k h
        exact (c.embedding i).injective (congrArg Subtype.val h)
      · intro j
        have hj : j.val ∈ Set.range (c.embedding i) := c.mem_range_embedding_iff'.mpr j.property.symm
        obtain ⟨k, hk⟩ := hj
        exact ⟨k, Subtype.ext hk⟩)
  simpa using (Fintype.card_congr he).symm

/-- Assign consecutive source variables to the descending blocks of the partition. -/
def canonicalMap (lam : Nat.Partition (Fintype.card σ)) :
    σ → Fin (descendingComposition lam).length :=
  (descendingComposition lam).index ∘ Fintype.equivFin σ

theorem canonicalMap_blockSize (lam : Nat.Partition (Fintype.card σ))
    (i : Fin (descendingComposition lam).length) :
    blockSize (canonicalMap lam) i = (descendingComposition lam).blocksFun i := by
  rw [canonicalMap, blockSize_comp_equiv, blockSize_composition_index]

theorem canonicalMap_rawParts (lam : Nat.Partition (Fintype.card σ)) :
    rawParts (canonicalMap (σ := σ) lam) = lam.parts := by
  unfold rawParts
  simp_rw [canonicalMap_blockSize]
  rw [Finset.val_univ_fin]
  change (((List.finRange (descendingComposition lam).length).map
    (descendingComposition lam).blocksFun : List ℕ) : Multiset ℕ) = lam.parts
  rw [← List.ofFn_eq_map, Composition.ofFn_blocksFun]
  exact Multiset.sort_eq _ _

/-- The chosen evaluation has exactly the requested genuine partition shape. -/
theorem canonicalMap_shape (lam : Nat.Partition (Fintype.card σ)) :
    shape (canonicalMap (σ := σ) lam) = lam := by
  apply Nat.Partition.ext
  rw [shape_parts, canonicalMap_rawParts]
  apply Multiset.filter_eq_self.mpr
  intro i hi
  exact (lam.parts_pos hi).ne'

/-- Canonical blocks are nonempty, so no artificial zero-size variables enter their Hilbert target. -/
theorem canonicalMap_surjective (lam : Nat.Partition (Fintype.card σ)) :
    Function.Surjective (canonicalMap (σ := σ) lam) := by
  intro i
  have hi := (descendingComposition lam).one_le_blocksFun i
  let j : Fin ((descendingComposition lam).blocksFun i) := ⟨0, by omega⟩
  refine ⟨(Fintype.equivFin σ).symm ((descendingComposition lam).embedding i j), ?_⟩
  simp [canonicalMap]

/-- Sorted part lists distinguish genuine partitions. -/
theorem sortedParts_injective {n : ℕ} :
    Function.Injective (fun p : Nat.Partition n ↦ p.parts.sort (· ≥ ·)) := by
  intro p q h
  apply Nat.Partition.ext
  simpa using congrArg (fun l : List ℕ ↦ (l : Multiset ℕ)) h

/-- A linear order whose strict relation is exactly the paper's descending-part lex order. -/
abbrev partitionLinearOrder (n : ℕ) : LinearOrder (Nat.Partition n) :=
  LinearOrder.lift' (fun p ↦ p.parts.sort (· ≥ ·)) sortedParts_injective

theorem partition_lt_iff {n : ℕ} (a b : Nat.Partition n) :
    @LT.lt (Nat.Partition n) (partitionLinearOrder n).toLT a b ↔ LexGreater b a := Iff.rfl

end
end VOA.GordonCanonicalPartitions
