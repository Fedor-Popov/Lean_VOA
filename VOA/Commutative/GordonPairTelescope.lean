/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonPairSuccessor
import VOA.Commutative.GordonPartitionBound

/-! # The full pair-filtration telescope on actual auxiliary quotient sectors -/

namespace VOA.GordonPairTelescope
open MvPolynomial VOA.GordonPairIndexing VOA.GordonPairSuccessor
open VOA.GordonRestrictedDual VOA.GordonFunctionalRelabel VOA.GordonPairedEvaluation
open VOA.GordonPairedRelations VOA.GordonPartitionBound VOA.GordonCommonFactors
open VOA.GordonCanonicalPartitions VOA.GordonFullDivisor
noncomputable section
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K]

abbrev PairCount (a b : ℕ) := Fin (min a b + 1)

instance model_finite (m D a b c : ℕ) :
    FiniteDimensional K (functionalModel (K := K) m D (originalColor a b c)) := by
  unfold functionalModel
  infer_instance

theorem pairCount_le_left (a b : ℕ) (R : PairCount a b) : R.val ≤ a := by
  have := Nat.min_le_left a b
  omega

theorem pairCount_le_right (a b : ℕ) (R : PairCount a b) : R.val ≤ b := by
  have := Nat.min_le_right a b
  omega

/-- Actual R-pair evaluation on one fixed finite-dimensional quotient-dual sector. -/
def modelPairEval (m D a b c : ℕ) (R : PairCount a b) :
    functionalModel (K := K) m D (originalColor a b c) →ₗ[K]
      MvPolynomial (Target (Fin R.val) (ResidualIndex a R.val) (ResidualIndex b R.val) (Fin c)) K :=
  (rename (pairedIndex a b c R.val (pairCount_le_left a b R) (pairCount_le_right a b R))).toLinearMap.domRestrict _

/-- The pair filtration is separated because its zero-pair evaluation is injective. -/
theorem pair_jointKernel_eq_bot (m D a b c : ℕ) :
    (⨅ R, (modelPairEval (K := K) m D a b c R).ker) = ⊥ := by
  apply VOA.GordonKernelFlag.iInf_ker_eq_bot_of_injective _ (⟨0, by omega⟩ : PairCount a b)
  intro F G h
  apply Subtype.ext
  exact rename_injective _ (pairedIndex_zero_injective a b c) h

/-- Later actual pair kernels supply every next residual collision required by Section 4. -/
theorem relabel_mem_nextSource (m D a b c : ℕ) (R : PairCount a b)
    (F : functionalModel (K := K) m D (originalColor a b c))
    (hF : F ∈ VOA.GordonKernelFlag.laterKernel (modelPairEval (K := K) m D a b c) R) :
    rename (sourceEquiv a b c R.val (pairCount_le_left a b R) (pairCount_le_right a b R)) F.val ∈
      nextSource m D := by
  let e := sourceEquiv a b c R.val (pairCount_le_left a b R) (pairCount_le_right a b R)
  have hmodel : rename e F.val ∈ functionalModel m D sourceColor :=
    rename_mem_functionalModel m D (originalColor a b c) sourceColor e
      (sourceEquiv_color a b c R.val _ _) F.val F.property
  rw [mem_nextSource]
  refine ⟨hmodel, ?_⟩
  intro x y
  have ha : R.val < a := lt_of_le_of_lt x.property x.val.isLt
  have hb : R.val < b := lt_of_le_of_lt y.property y.val.isLt
  let S : PairCount a b := ⟨R.val + 1, by omega⟩
  have hz := VOA.GordonKernelFlag.laterKernel_le_ker (modelPairEval (K := K) m D a b c)
    (show R < S by exact Nat.lt_succ_self _) hF
  have hnext := nextPairEval_eq_zero_of_successor a b c R.val ha hb F.val hz
  apply (collisionFactor_dvd_iff _ _ (by simp [eLabel, fLabel]) _).mp
  exact residual_factor_dvd (firstResidual a R.val ha) x (firstResidual b R.val hb) y
    (rename e F.val) (functionalModel_residual_symmetry m D _ hmodel) hnext

/-- The actual R-th restricted evaluation image is contained in the paired image
whose partition Hilbert bound has already been proved. -/
theorem pairRange_le_pairedImage (m D a b c : ℕ) (R : PairCount a b) :
    (VOA.GordonKernelFlag.restrictedEvaluation (modelPairEval (K := K) m D a b c) R).range ≤
      pairedImage (K := K) (ρ := Fin R.val) (α := ResidualIndex a R.val)
        (β := ResidualIndex b R.val) (γ := Fin c) m D := by
  rintro x ⟨F, rfl⟩
  refine ⟨rename (sourceEquiv a b c R.val (pairCount_le_left a b R)
    (pairCount_le_right a b R)) F.val.val, relabel_mem_nextSource m D a b c R F.val F.property, ?_⟩
  change pairEval (rename _ F.val.val) = rename (pairedIndex a b c R.val _ _) F.val.val
  simp only [pairEval, rename_rename, pairedIndex]

/-- The exact pair-filtration telescope on the actual quotient sector. -/
theorem sector_finrank_eq_sum_pair_images (m D a b c : ℕ) :
    Module.finrank K (sector (K := K) m D (originalColor a b c)) =
      ∑ R : PairCount a b, Module.finrank K
        (VOA.GordonKernelFlag.restrictedEvaluation (modelPairEval (K := K) m D a b c) R).range := by
  rw [← finrank_functionalModel]
  exact VOA.GordonFiniteOrderedKernelFlag.finrank_eq_sum_restrictedRanges
    (modelPairEval (K := K) m D a b c) (pair_jointKernel_eq_bot (K := K) m D a b c)

/-- Complete Section 3–4 upper bound for an actual fixed-particle auxiliary quotient sector. -/
theorem sector_finrank_le_pair_partition_sum (m D a b c : ℕ) :
    (Module.finrank K (sector (K := K) m D (originalColor a b c)) : ℚ) ≤
      ∑ R : PairCount a b,
        ∑ lam : {lam : Nat.Partition (Fintype.card (Fin R.val)) // ∀ i ∈ lam.parts, i ≤ m},
          PowerSeries.coeff D
            (PowerSeries.X ^ fullDegree (α := ResidualIndex a R.val)
              (β := ResidualIndex b R.val) (γ := Fin c) m (canonicalMap (σ := Fin R.val) lam.val) *
              invariantSeries (α := ResidualIndex a R.val) (β := ResidualIndex b R.val)
                (γ := Fin c) (canonicalMap (σ := Fin R.val) lam.val)) := by
  rw [sector_finrank_eq_sum_pair_images, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R _
  have h := pairedImage_finrank_le_bounded_partition_sum (K := K) (ρ := Fin R.val)
    (α := ResidualIndex a R.val) (β := ResidualIndex b R.val) (γ := Fin c) m D
  exact (Nat.cast_le.mpr (Submodule.finrank_mono (pairRange_le_pairedImage m D a b c R))).trans h

end
end VOA.GordonPairTelescope
