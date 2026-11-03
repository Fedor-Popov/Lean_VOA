/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.IteratedBlockSymmetricInvariant
import VOA.Commutative.WeightedPolynomialHilbert

/-! # The actual grading in blockwise symmetric polynomial presentations -/
namespace VOA.BlockSymmetricWeightedDegree
open MvPolynomial IteratedBlockSymmetricInvariant BlockwiseSymmetricInvariantInduction
noncomputable section
variable {K : Type*} [Field K]

/-- Elementary generators in each block have successive weights 1,...,a. -/
def blockWeight : (blocks : List ℕ) → BlockSlots blocks → ℕ
  | [], i => Fin.elim0 i
  | _ :: _, Sum.inl i => i.val + 1
  | _ :: rest, Sum.inr i => blockWeight rest i

theorem blockWeight_pos (blocks : List ℕ) (i : BlockSlots blocks) : 0 < blockWeight blocks i := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons a rest ih =>
    rcases i with i | i
    · exact Nat.succ_pos _
    · exact ih i

set_option backward.isDefEq.respectTransparency false in
/-- The new block's generators are its elementary symmetric polynomials. -/
theorem blockEsymm_X_inl (a : ℕ) (rest : List ℕ) (i : Fin a) :
    (blockEsymmAlgEquiv (K := K) (a :: rest) (X (Sum.inl i))).val =
      rename Sum.inl (esymm (Fin a) K (i.val + 1)) := by
  simp [blockEsymmAlgEquiv, extendFixedPresentation, consFixedAlgEquiv,
    extendedToConsFixed, nestedFixedExtendedAlgEquiv, nestedFixedToExtended,
    nestedFixedToExtendedRaw, nestedFixedVal, esymmAlgEquiv_apply, esymmAlgHom, sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial]
  apply (sumAlgEquiv K (Fin a) (BlockSlots rest)).injective
  rw [sumToIter_Xl]
  simp [map_esymm]
  have he := DFunLike.congr_fun
    (sumAlgEquiv_comp_rename_inl (R := K) (S₁ := Fin a) (S₂ := BlockSlots rest))
    (esymm (Fin a) K (i.val + 1))
  simpa [map_esymm] using he.symm

set_option backward.isDefEq.respectTransparency false in
/-- Tail generators retain their old symmetric-polynomial expressions. -/
theorem blockEsymm_X_inr (a : ℕ) (rest : List ℕ) (i : BlockSlots rest) :
    (blockEsymmAlgEquiv (K := K) (a :: rest) (X (Sum.inr i))).val =
      rename Sum.inr (blockEsymmAlgEquiv (K := K) rest (X i)).val := by
  simp [blockEsymmAlgEquiv, extendFixedPresentation, consFixedAlgEquiv,
    extendedToConsFixed, nestedFixedExtendedAlgEquiv, nestedFixedToExtended,
    nestedFixedToExtendedRaw, nestedFixedVal, tailFixedAlgEquiv,
    esymmAlgEquiv_apply, esymmAlgHom, sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial]
  apply (sumAlgEquiv K (Fin a) (BlockSlots rest)).injective
  rw [sumToIter_Xr]
  simp
  have he := DFunLike.congr_fun
    (sumAlgEquiv_comp_rename_inr (R := K) (S₁ := Fin a) (S₂ := BlockSlots rest))
    (blockEsymmAlgEquiv (K := K) rest (X i)).val
  simpa using he.symm

/-- Every actual generator image has its assigned ordinary degree. -/
theorem blockEsymm_X_homogeneous (blocks : List ℕ) (i : BlockSlots blocks) :
    ((blockEsymmAlgEquiv (K := K) blocks (X i)).val).IsHomogeneous (blockWeight blocks i) := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons a rest ih =>
    rcases i with i | i
    · rw [blockEsymm_X_inl]
      exact (SymmetricWeightedDegree.esymm_isHomogeneous (i.val + 1)).rename_isHomogeneous
    · rw [blockEsymm_X_inr]
      exact (ih i).rename_isHomogeneous

/-- Forgetting invariance in the actual block presentation is evaluation
at the proved homogeneous generator images. -/
theorem blockEsymm_apply_eq_aeval (blocks : List ℕ)
    (p : MvPolynomial (BlockSlots blocks) K) :
    (blockEsymmAlgEquiv (K := K) blocks p).val =
      aeval (fun i => (blockEsymmAlgEquiv (K := K) blocks (X i)).val) p := by
  let F := (blockFixedSubalgebra (K := K) blocks).val.comp
    (blockEsymmAlgEquiv (K := K) blocks).toAlgHom
  have he : F = aeval (fun i => F (X i)) := by ext i; simp
  exact AlgHom.congr_fun he p

/-- The block elementary presentation preserves and reflects its positive
weighted grading. -/
theorem blockEsymm_homogeneous_iff (blocks : List ℕ)
    (p : MvPolynomial (BlockSlots blocks) K) (d : ℕ) :
    (blockEsymmAlgEquiv (K := K) blocks p).val.IsHomogeneous d ↔
      p.IsWeightedHomogeneous (blockWeight blocks) d := by
  rw [blockEsymm_apply_eq_aeval]
  constructor
  · apply SymmetricWeightedDegree.weightedHomogeneous_of_aeval _ _
      (blockEsymm_X_homogeneous blocks)
    intro p q he
    apply (blockEsymmAlgEquiv (K := K) blocks).injective
    apply Subtype.ext
    simpa only [← blockEsymm_apply_eq_aeval] using he
  · exact SymmetricWeightedDegree.aeval_weightedHomogeneous _ _
      (blockEsymm_X_homogeneous blocks) p d

/-- The homogeneous part of the actual block-symmetric invariant algebra. -/
def blockInvariantPiece (blocks : List ℕ) (d : ℕ) :
    Submodule K (MvPolynomial (BlockSlots blocks) K) :=
  (blockFixedSubalgebra (K := K) blocks).toSubmodule ⊓
    homogeneousSubmodule (BlockSlots blocks) K d

/-- The elementary block presentation is a linear isomorphism on each
specified ordinary degree, with positive weighted source degrees. -/
def blockDegreeEquiv (blocks : List ℕ) (d : ℕ) :
    weightedHomogeneousSubmodule K (blockWeight blocks) d ≃ₗ[K]
      blockInvariantPiece (K := K) blocks d where
  toFun p := ⟨(blockEsymmAlgEquiv (K := K) blocks p.val).val,
    (blockEsymmAlgEquiv (K := K) blocks p.val).property,
    (blockEsymm_homogeneous_iff blocks p.val d).mpr p.property⟩
  invFun p := ⟨(blockEsymmAlgEquiv (K := K) blocks).symm ⟨p.val, p.property.1⟩, by
    apply (blockEsymm_homogeneous_iff blocks _ d).mp
    rw [AlgEquiv.apply_symm_apply]
    exact p.property.2⟩
  left_inv p := by apply Subtype.ext; exact (blockEsymmAlgEquiv blocks).symm_apply_apply _
  right_inv p := by
    apply Subtype.ext
    exact congrArg (fun t : blockFixedSubalgebra (K := K) blocks => t.val)
      ((blockEsymmAlgEquiv blocks).apply_symm_apply ⟨p.val, p.property.1⟩)
  map_add' p q := by apply Subtype.ext; simp
  map_smul' c p := by apply Subtype.ext; simp

/-- Exact block-invariant dimension as a weighted monomial count. -/
theorem blockInvariantPiece_finrank (blocks : List ℕ) (d : ℕ) :
    Module.finrank K (blockInvariantPiece (K := K) blocks d) =
      Nat.card {e : BlockSlots blocks →₀ ℕ // Finsupp.weight (blockWeight blocks) e = d} := by
  rw [← (blockDegreeEquiv (K := K) blocks d).finrank_eq]
  exact SymmetricWeightedDegree.weightedPiece_finrank _
    (fun i => Nat.ne_of_gt (blockWeight_pos blocks i)) d

/-- The elementary weights factor into one reciprocal q-factorial per
block; this is an identity of actual formal series. -/
theorem blockWeight_geometric_product (blocks : List ℕ) :
    (∏ i : BlockSlots blocks, QSeries.weightedGeometric (R := ℚ) (blockWeight blocks i)) =
      (blocks.map (fun n => (QSeries.reciprocalQFactorial n : PowerSeries ℚ))).prod := by
  induction blocks with
  | nil => simp [BlockSlots]
  | cons a rest ih =>
    change (∏ i : Fin a ⊕ BlockSlots rest,
      QSeries.weightedGeometric (R := ℚ) (blockWeight (a :: rest) i)) = _
    rw [Fintype.prod_sum_type]
    change (∏ i : Fin a, QSeries.weightedGeometric (R := ℚ) (i.val + 1)) *
      (∏ i : BlockSlots rest, QSeries.weightedGeometric (R := ℚ) (blockWeight rest i)) = _
    rw [QSeries.prod_weightedGeometric_eq_reciprocalQFactorial, ih]
    rfl

/-- The exact degreewise Hilbert series of the actual finite-block fixed
polynomial algebra, with one reciprocal factorial per block. -/
theorem blockInvariantPiece_finrank_eq_coeff (blocks : List ℕ) (d : ℕ) :
    (Module.finrank K (blockInvariantPiece (K := K) blocks d) : ℚ) =
      PowerSeries.coeff d
        ((blocks.map (fun n => (QSeries.reciprocalQFactorial n : PowerSeries ℚ))).prod) := by
  rw [blockInvariantPiece_finrank, ← blockWeight_geometric_product,
    QSeries.coeff_prod_weightedGeometric_eq_card _ (blockWeight_pos blocks)]

end
end VOA.BlockSymmetricWeightedDegree
