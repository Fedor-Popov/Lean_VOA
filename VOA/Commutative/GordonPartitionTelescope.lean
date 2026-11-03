/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonCanonicalEvaluation
import VOA.Commutative.GordonFiniteOrderedKernelFlag

/-! # The genuine partition-indexed Gordon filtration and exact dimension telescope -/

namespace VOA.GordonPartitionTelescope

open MvPolynomial VOA.GordonFiltration VOA.GordonCanonicalPartitions
open VOA.GordonCanonicalEvaluation VOA.GordonResidualFiltration VOA.GordonPartitionOrder

noncomputable section

variable {σ δ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

local instance partitionOrder (n : ℕ) : LinearOrder (Nat.Partition n) := partitionLinearOrder n

/-- The actual canonical evaluation for every genuine partition, with a dependent target. -/
def partitionEval (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (lam : Nat.Partition (Fintype.card σ)) :
    U →ₗ[K] MvPolynomial (Fin (descendingComposition lam).length ⊕ δ) K :=
  (residualEval (canonicalMap lam)).toLinearMap.domRestrict U

/-- Later canonical partition kernels imply every higher block-assignment kernel,
even when its output label type has a different cardinality. -/
theorem laterKernel_mem_residualFiltration {τ : Type*} [Fintype τ] [DecidableEq τ]
    (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (hsym : ∀ F ∈ U, ∀ e : Equiv.Perm σ,
      rename (Equiv.sumCongr e (Equiv.refl δ)) F = F)
    (lam : Nat.Partition (Fintype.card σ)) (F : U)
    (hF : F ∈ VOA.GordonKernelFlag.laterKernel (partitionEval U) lam) :
    F.val ∈ residualFiltration (τ := τ) U lam := by
  rw [mem_residualFiltration]
  refine ⟨F.property, ?_⟩
  intro f hf
  apply residualEval_eq_zero_of_canonical f F.val (hsym F.val F.property)
  exact VOA.GordonKernelFlag.laterKernel_le_ker (partitionEval U)
    ((partition_lt_iff lam (shape f)).mpr hf) hF

/-- All canonical evaluations jointly separate symmetric polynomials: the singleton
partition recovers the identity assignment. -/
theorem jointKernel_eq_bot (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (hsym : ∀ F ∈ U, ∀ e : Equiv.Perm σ,
      rename (Equiv.sumCongr e (Equiv.refl δ)) F = F) :
    (⨅ lam, (partitionEval U lam).ker) = ⊥ := by
  apply bot_unique
  intro F hF
  have hz : residualEval (canonicalMap (shape (id : σ → σ))) F.val = 0 :=
    ((Submodule.mem_iInf _).mp hF) (shape (id : σ → σ))
  have h := residualEval_eq_zero_of_canonical (id : σ → σ) F.val
    (hsym F.val F.property) hz
  rw [Submodule.mem_bot]
  apply Subtype.ext
  simpa [residualEval] using h

/-- The rank of a symmetric source is exactly the sum of its genuine Gordon layers.
There are no extra variables from empty blocks and no fixed-length partition restriction. -/
theorem finrank_eq_sum_partition_images
    (U : Submodule K (MvPolynomial (σ ⊕ δ) K)) [FiniteDimensional K U]
    (hsym : ∀ F ∈ U, ∀ e : Equiv.Perm σ,
      rename (Equiv.sumCongr e (Equiv.refl δ)) F = F) :
    Module.finrank K U = ∑ lam : Nat.Partition (Fintype.card σ),
      Module.finrank K (VOA.GordonKernelFlag.restrictedEvaluation (partitionEval U) lam).range :=
  VOA.GordonFiniteOrderedKernelFlag.finrank_eq_sum_restrictedRanges (partitionEval U)
    (jointKernel_eq_bot U hsym)

end
end VOA.GordonPartitionTelescope
