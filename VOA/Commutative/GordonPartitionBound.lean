/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import VOA.Commutative.GordonInvariantHilbert
import VOA.Commutative.GordonPartitionTelescope

/-! # The full Gordon Hilbert bound summed over genuine partitions -/

namespace VOA.GordonPartitionBound

open MvPolynomial VOA.GordonRestrictedDual VOA.GordonPairedEvaluation
open VOA.GordonPairedRelations VOA.GordonResidualFiltration VOA.GordonFullDivisor
open VOA.GordonFullQuotient VOA.GordonCanonicalPartitions VOA.GordonPartitionTelescope
open VOA.GordonFiltration

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {ρ τ α β γ : Type} [Fintype ρ] [Fintype τ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder τ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

local instance partitionOrder (n : ℕ) : LinearOrder (Nat.Partition n) := partitionLinearOrder n

/-- Actual source polynomials killed by the next-pair evaluations. -/
def nextSource (m D : ℕ) : Submodule K (MvPolynomial (Source ρ α β γ) K) :=
  functionalModel m D sourceColor ⊓
    ⨅ x : α, ⨅ y : β, (nextPairEval (K := K) (ρ := ρ) (γ := γ) x y).toLinearMap.ker

@[simp] theorem mem_nextSource (m D : ℕ) (F : MvPolynomial (Source ρ α β γ) K) :
    F ∈ nextSource m D ↔ F ∈ functionalModel m D sourceColor ∧
      ∀ x : α, ∀ y : β, nextPairEval x y F = 0 := by
  simp [nextSource, LinearMap.mem_ker]

instance nextSource_finite (m D : ℕ) :
    FiniteDimensional K (nextSource (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D) := by
  letI := VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_homogeneousSubmodule
    (K := K) (I := Source ρ α β γ) D
  have hle : nextSource (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D ≤
      homogeneousSubmodule (Source ρ α β γ) K D := by
    intro F hF
    obtain ⟨L, rfl⟩ := ((mem_nextSource m D F).mp hF).1
    exact particleMap_homogeneous _ _ _ _
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

instance sourceStep_finite (m D : ℕ) (f : ρ → τ) :
    FiniteDimensional K (sourceStep (K := K) (α := α) (β := β) (γ := γ) m D f) := by
  have hle : sourceStep (K := K) (α := α) (β := β) (γ := γ) m D f ≤ nextSource m D := by
    intro F hF
    have h := (mem_sourceStep m D f F).mp hF
    exact (mem_nextSource m D F).mpr ⟨h.1, h.2.1⟩
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- The actual paired image on one pair-filtration layer. -/
def pairedImage (m D : ℕ) : Submodule K (MvPolynomial (Target ρ α β γ) K) :=
  (nextSource m D).map pairEval.toLinearMap

instance pairedImage_finite (m D : ℕ) :
    FiniteDimensional K (pairedImage (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D) := by
  unfold pairedImage
  infer_instance

theorem pairedImage_symmetry (m D : ℕ) (F : MvPolynomial (Target ρ α β γ) K)
    (hF : F ∈ pairedImage m D) (e : Equiv.Perm ρ) :
    rename (Equiv.sumCongr e (Equiv.refl (Residual α β γ))) F = F := by
  obtain ⟨G, hG, rfl⟩ := hF
  exact functionalModel_pair_symmetry m D G ((mem_nextSource m D G).mp hG).1 e

/-- Reciprocal factorial series of the proved full invariant target. -/
def invariantSeries (f : ρ → τ) : PowerSeries ℚ :=
  (∏ i : Fin (Fintype.card ρ + 1),
    QSeries.reciprocalQFactorial (Nat.card {j // blockSize f j = i.val})) *
    QSeries.reciprocalQFactorial (Fintype.card α) *
    QSeries.reciprocalQFactorial (Fintype.card β) *
    QSeries.reciprocalQFactorial (Fintype.card γ)

/-- A nonzero image must have at least the full divisor degree. -/
theorem fullDegree_le_of_image_ne_zero (m D : ℕ) (f : ρ → τ)
    (x : (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range)
    (hx : x.val ≠ 0) : fullDegree (α := α) (β := β) (γ := γ) m f ≤ D := by
  obtain ⟨q, hq⟩ := image_exists_quotient m D f x
  have hd := totalDegree_le_of_dvd_of_isDomain (show fullDivisor m f ∣ x.val from ⟨q.val, hq⟩) hx
  rw [(fullDivisor_isHomogeneous m f).totalDegree (fullDivisor_ne_zero m f)] at hd
  have hh : x.val.IsHomogeneous D := by
    obtain ⟨F, hF⟩ := x.property
    rw [← hF]
    obtain ⟨L, hL⟩ := ((mem_sourceStep m D f F.val).mp F.property).1
    change (clusterEval f F.val).IsHomogeneous D
    rw [← hL]
    exact (particleMap_homogeneous _ _ _ L).rename_isHomogeneous
  rwa [hh.totalDegree hx] at hd

/-- Uniform degreewise bound, including the degrees below the divisor. -/
theorem stepRange_finrank_le_coeff (m D : ℕ) (f : ρ → τ) :
    (Module.finrank K (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range : ℚ) ≤
      PowerSeries.coeff D (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) m f *
        invariantSeries (α := α) (β := β) (γ := γ) f) := by
  by_cases hd : fullDegree (α := α) (β := β) (γ := γ) m f ≤ D
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [PowerSeries.coeff_X_pow_mul', if_pos hd, Nat.add_sub_cancel_left]
    change _ ≤ PowerSeries.coeff r (invariantSeries (α := α) (β := β) (γ := γ) f)
    rw [invariantSeries, ← fullInvariantPiece_finrank_eq_coeff
      (K := K) (α := α) (β := β) (γ := γ) f r]
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective
      (gradedImageMap_injective (K := K) (α := α) (β := β) (γ := γ) m r f)
  · have hz : (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range = ⊥ := by
      apply bot_unique
      intro x hx
      rw [Submodule.mem_bot]
      by_contra h
      exact hd (fullDegree_le_of_image_ne_zero m D f ⟨x, hx⟩ h)
    rw [hz, finrank_bot, Nat.cast_zero, PowerSeries.coeff_X_pow_mul', if_neg hd]

/-- Each genuine partition layer lands in the actual full source-step image. -/
theorem partitionRange_le_stepRange (m D : ℕ) (lam : Nat.Partition (Fintype.card ρ)) :
    (VOA.GordonKernelFlag.restrictedEvaluation
      (partitionEval (pairedImage (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D)) lam).range ≤
      (stepEval (K := K) (α := α) (β := β) (γ := γ) m D (canonicalMap lam)).range := by
  rintro x ⟨F, rfl⟩
  obtain ⟨G, hG, hGF⟩ := F.val.property
  change pairEval G = F.val.val at hGF
  have hmem := laterKernel_mem_residualFiltration
    (τ := Fin (descendingComposition lam).length) _ (pairedImage_symmetry m D) lam F.val F.property
  have hstep : G ∈ sourceStep m D (canonicalMap lam) := by
    rw [mem_sourceStep]
    refine ⟨((mem_nextSource m D G).mp hG).1, ((mem_nextSource m D G).mp hG).2, ?_⟩
    rw [canonicalMap_shape]
    rw [mem_residualFiltration] at hmem ⊢
    exact ⟨Submodule.mem_top, by simpa only [hGF] using hmem.2⟩
  refine ⟨⟨G, hstep⟩, ?_⟩
  change clusterEval (canonicalMap lam) G = residualEval (canonicalMap lam) F.val.val
  rw [clusterEval_eq, hGF]

/-- The complete Gordon bound on an actual pair-filtration image, summed over
all genuine partitions of the paired-particle number. -/
theorem pairedImage_finrank_le_partition_sum (m D : ℕ) :
    (Module.finrank K (pairedImage (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D) : ℚ) ≤
      ∑ lam : Nat.Partition (Fintype.card ρ), PowerSeries.coeff D
        (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) m (canonicalMap lam) *
          invariantSeries (α := α) (β := β) (γ := γ) (canonicalMap lam)) := by
  rw [finrank_eq_sum_partition_images _ (pairedImage_symmetry m D), Nat.cast_sum]
  apply Finset.sum_le_sum
  intro lam _
  exact (Nat.cast_le.mpr (Submodule.finrank_mono (partitionRange_le_stepRange m D lam))).trans
    (stepRange_finrank_le_coeff m D (canonicalMap lam))

/-- A partition containing a block larger than the relation length contributes zero. -/
theorem partitionRange_eq_bot_of_large_part (m D : ℕ)
    (lam : Nat.Partition (Fintype.card ρ)) (hlarge : ¬ ∀ i ∈ lam.parts, i ≤ m) :
    (VOA.GordonKernelFlag.restrictedEvaluation
      (partitionEval (pairedImage (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D)) lam).range = ⊥ := by
  classical
  push_neg at hlarge
  obtain ⟨i, hi, hmi⟩ := hlarge
  rw [← canonicalMap_rawParts (σ := ρ) lam] at hi
  obtain ⟨u, _, hu⟩ := Multiset.mem_map.mp hi
  apply bot_unique
  rintro x ⟨F, rfl⟩
  obtain ⟨G, hG, hGF⟩ := F.val.property
  change pairEval G = F.val.val at hGF
  rw [Submodule.mem_bot]
  change residualEval (canonicalMap lam) F.val.val = 0
  rw [← hGF, ← clusterEval_eq]
  exact large_block_eval_eq_zero m D (canonicalMap lam) u (by omega) G
    ((mem_nextSource m D G).mp hG).1

/-- Only partitions whose parts are at most the actual auxiliary relation length
occur in the global Gordon upper bound. -/
theorem pairedImage_finrank_le_bounded_partition_sum (m D : ℕ) :
    (Module.finrank K (pairedImage (K := K) (ρ := ρ) (α := α) (β := β) (γ := γ) m D) : ℚ) ≤
      ∑ lam : {lam : Nat.Partition (Fintype.card ρ) // ∀ i ∈ lam.parts, i ≤ m},
        PowerSeries.coeff D
          (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) m (canonicalMap lam.val) *
            invariantSeries (α := α) (β := β) (γ := γ) (canonicalMap lam.val)) := by
  classical
  rw [finrank_eq_sum_partition_images _ (pairedImage_symmetry m D), Nat.cast_sum]
  rw [← Finset.subtype_univ,
    Finset.sum_subtype_eq_sum_filter (fun lam : Nat.Partition (Fintype.card ρ) ↦
      PowerSeries.coeff D
        (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) m (canonicalMap lam) *
          invariantSeries (α := α) (β := β) (γ := γ) (canonicalMap lam))), Finset.sum_filter]
  apply Finset.sum_le_sum
  intro lam _
  by_cases h : ∀ i ∈ lam.parts, i ≤ m
  · rw [if_pos h]
    exact (Nat.cast_le.mpr (Submodule.finrank_mono (partitionRange_le_stepRange m D lam))).trans
      (stepRange_finrank_le_coeff m D (canonicalMap lam))
  · rw [if_neg h, partitionRange_eq_bot_of_large_part m D lam h, finrank_bot, Nat.cast_zero]

end
end VOA.GordonPartitionBound
