/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonCanonicalPartitions

/-! # Canonical partition evaluations determine every symmetric block evaluation -/

namespace VOA.GordonCanonicalEvaluation

open MvPolynomial VOA.GordonFiltration VOA.GordonBlockEquiv
open VOA.GordonCanonicalPartitions VOA.GordonResidualFiltration

noncomputable section

variable {σ τ υ δ K : Type*} [Fintype σ] [Fintype τ] [Fintype υ]
variable [DecidableEq σ] [DecidableEq τ] [DecidableEq υ] [CommRing K]

theorem blockSize_pos_of_surjective (f : σ → τ) (hf : Function.Surjective f) (j : τ) :
    0 < blockSize f j := by
  rw [blockSize_eq_card_fiber, Fintype.card_pos_iff]
  obtain ⟨i, hi⟩ := hf j
  exact ⟨⟨i, hi⟩⟩

theorem shape_parts_of_surjective (f : σ → τ) (hf : Function.Surjective f) :
    (shape f).parts = rawParts f := by
  rw [shape_parts]
  apply Multiset.filter_eq_self.mpr
  intro n hn
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hn
  exact (blockSize_pos_of_surjective f hf j).ne'

/-- Equal multisets of block sizes produce an actual matching of block labels. -/
def labelEquiv (f : σ → τ) (g : σ → υ) (h : rawParts f = rawParts g) : τ ≃ υ :=
  Equiv.ofFiberEquiv (fun n ↦ Fintype.equivOfCardEq (by
    have hn := congrArg (Multiset.count n) h
    simpa only [rawParts, Multiset.count_map, ← Finset.filter_val,
      Finset.card_val, Fintype.card_subtype, eq_comm] using hn))

theorem labelEquiv_size (f : σ → τ) (g : σ → υ) (h : rawParts f = rawParts g) (j : τ) :
    blockSize g (labelEquiv f g h j) = blockSize f j :=
  Equiv.ofFiberEquiv_map _ j

/-- Symmetry identifies any surjective block evaluation with the canonical
partition evaluation, after a genuine relabeling of the output variables. -/
theorem residualEval_eq_canonical (f : σ → τ) (hf : Function.Surjective f)
    (F : MvPolynomial (σ ⊕ δ) K)
    (hsym : ∀ e : Equiv.Perm σ, rename (Equiv.sumCongr e (Equiv.refl δ)) F = F) :
    ∃ e : Fin (descendingComposition (shape f)).length ≃ τ,
      residualEval f F = rename (Sum.map e id) (residualEval (canonicalMap (shape f)) F) := by
  have h : rawParts (canonicalMap (σ := σ) (shape f)) = rawParts f := by
    rw [canonicalMap_rawParts, shape_parts_of_surjective f hf]
  let e := labelEquiv (canonicalMap (σ := σ) (shape f)) f h
  refine ⟨e, ?_⟩
  apply (sumRingEquiv K τ δ).injective
  change sumToIter K τ δ (residualEval f F) =
    sumToIter K τ δ (residualEval e (residualEval (canonicalMap (shape f)) F))
  rw [sumToIter_residualEval, sumToIter_residualEval, sumToIter_residualEval]
  change blockEval f _ = rename e (rename (canonicalMap (shape f)) _)
  rw [rename_rename]
  apply blockEval_eq_of_blockSize_eq _ _ _ (sumToIter_isSymmetric F hsym)
  intro j
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [blockSize_equiv_comp]
  exact labelEquiv_size _ _ h i

/-- The actual nonempty block labels of a possibly nonsurjective assignment. -/
abbrev Active (f : σ → τ) := {j : τ // 0 < blockSize f j}

def activeMap (f : σ → τ) (i : σ) : Active f := ⟨f i, by
  rw [blockSize_eq_card_fiber, Fintype.card_pos_iff]
  exact ⟨⟨i, rfl⟩⟩⟩

theorem activeMap_surjective (f : σ → τ) : Function.Surjective (activeMap f) := by
  intro j
  have hj := j.property
  rw [blockSize_eq_card_fiber, Fintype.card_pos_iff] at hj
  obtain ⟨i⟩ := hj
  exact ⟨i.val, Subtype.ext i.property⟩

theorem activeMap_blockSize (f : σ → τ) (j : Active f) :
    blockSize (activeMap f) j = blockSize f j.val := by
  unfold blockSize
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Subtype.ext_iff

theorem activeMap_shape (f : σ → τ) : shape (activeMap f) = shape f := by
  apply Nat.Partition.ext
  rw [shape_parts_of_surjective _ (activeMap_surjective f), shape_parts]
  apply Multiset.ext.mpr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [Multiset.count_eq_zero.mpr]
    · simp
    · intro h
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp h
      rw [activeMap_blockSize] at hj
      exact j.property.ne' hj
  · rw [Multiset.count_filter_of_pos (p := fun x : ℕ ↦ x ≠ 0) hn]
    have he : {j : Active f // blockSize (activeMap f) j = n} ≃
        {j : τ // blockSize f j = n} :=
      { toFun := fun j ↦ ⟨j.val.val, by simpa [activeMap_blockSize] using j.property⟩
        invFun := fun j ↦ ⟨⟨j.val, by rw [j.property]; omega⟩, by
          simpa [activeMap_blockSize] using j.property⟩
        left_inv := fun j ↦ rfl
        right_inv := fun j ↦ rfl }
    simpa only [rawParts, Multiset.count_map, ← Finset.filter_val,
      Finset.card_val, Fintype.card_subtype, eq_comm] using Fintype.card_congr he

/-- A canonical zero evaluation forces every assignment with that partition to vanish. -/
theorem residualEval_eq_zero_of_canonical (f : σ → τ) (F : MvPolynomial (σ ⊕ δ) K)
    (hsym : ∀ e : Equiv.Perm σ, rename (Equiv.sumCongr e (Equiv.refl δ)) F = F)
    (hz : residualEval (canonicalMap (shape f)) F = 0) : residualEval f F = 0 := by
  have hz' : residualEval (canonicalMap (shape (activeMap f))) F = 0 := by
    exact (congrArg (fun lam : Nat.Partition (Fintype.card σ) ↦
      residualEval (canonicalMap lam) F = 0) (activeMap_shape f)).mpr hz
  obtain ⟨e, he⟩ := residualEval_eq_canonical (activeMap f) (activeMap_surjective f) F hsym
  rw [hz', map_zero] at he
  have h := congrArg (rename (Sum.map (Subtype.val : Active f → τ) id)) he
  simpa [residualEval, rename_rename, activeMap, Function.comp_def] using h

end
end VOA.GordonCanonicalEvaluation
