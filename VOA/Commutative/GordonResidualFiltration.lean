/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonDivisor

/-! # Gordon kernels with independent residual particle variables

The filtration remains linear over the ground field. Residual variables are retained
as polynomial parameters during occupancy interpolation; no closure of the source
space under multiplication by arbitrary residual polynomials is assumed.
-/

namespace VOA.GordonResidualFiltration

open MvPolynomial VOA.GordonFiltration VOA.GordonPartitionOrder
open VOA.GordonArbitraryPair

noncomputable section

variable {K σ τ δ : Type*} [CommRing K]
variable [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

/-- Evaluate the cluster blocks while retaining every residual variable. -/
def residualEval (f : σ → τ) : MvPolynomial (σ ⊕ δ) K →ₐ[K] MvPolynomial (τ ⊕ δ) K :=
  rename (Sum.map f id)

/-- The actual Gordon filtration on a ground-field-linear particle subspace. -/
def residualFiltration (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (lam : Nat.Partition (Fintype.card σ)) : Submodule K (MvPolynomial (σ ⊕ δ) K) :=
  U ⊓ ⨅ f : σ → τ, ⨅ (_ : LexGreater (shape f) lam), (residualEval f).toLinearMap.ker

@[simp] theorem mem_residualFiltration (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (lam : Nat.Partition (Fintype.card σ)) (F : MvPolynomial (σ ⊕ δ) K) :
    F ∈ residualFiltration (τ := τ) U lam ↔
      F ∈ U ∧ ∀ f : σ → τ, LexGreater (shape f) lam → residualEval f F = 0 := by
  simp [residualFiltration, LinearMap.mem_ker]

/-- Residual variables can be moved into the coefficient ring before evaluating blocks. -/
theorem sumToIter_residualEval (f : σ → τ) (F : MvPolynomial (σ ⊕ δ) K) :
    sumToIter K τ δ (residualEval f F) = blockEval f (sumToIter K σ δ F) := by
  have hhom : (sumToIter K τ δ).comp (residualEval f).toRingHom =
      (blockEval f).toRingHom.comp (sumToIter K σ δ) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [residualEval, blockEval]
    · rintro (i | i) <;> simp [residualEval, blockEval]
  exact DFunLike.congr_fun hhom F

/-- Tau symmetry persists over the formal residual coefficient ring. -/
theorem sumToIter_isSymmetric (F : MvPolynomial (σ ⊕ δ) K)
    (hsym : ∀ e : Equiv.Perm σ, rename (Equiv.sumCongr e (Equiv.refl δ)) F = F) :
    (sumToIter K σ δ F).IsSymmetric := by
  intro e
  change blockEval e (sumToIter K σ δ F) = _
  rw [← sumToIter_residualEval]
  change sumToIter K σ δ (rename (Equiv.sumCongr e (Equiv.refl δ)) F) = _
  rw [hsym]

/-- The actual ground-field Gordon kernels imply the coefficient-ring kernels
needed by the occupancy theorem, without a residual-module closure assumption. -/
theorem sumToIter_mem_filtration (U : Submodule K (MvPolynomial (σ ⊕ δ) K))
    (lam : Nat.Partition (Fintype.card σ)) (F : MvPolynomial (σ ⊕ δ) K)
    (hF : F ∈ residualFiltration (τ := τ) U lam) :
    sumToIter K σ δ F ∈ filtration (τ := τ)
      (⊤ : Submodule (MvPolynomial δ K) (MvPolynomial σ (MvPolynomial δ K))) lam := by
  rw [mem_filtration]
  refine ⟨Submodule.mem_top, ?_⟩
  intro f hf
  rw [← sumToIter_residualEval,
    ((mem_residualFiltration U lam F).mp hF).2 f hf, map_zero]

/-- Full multivariate cluster-difference multiplicity with independent residual variables. -/
theorem cluster_factor_dvd [Algebra ℚ K] [IsDomain K] [CharZero K]
    (f : σ → τ) (u v : τ) (huv : u ≠ v)
    (U : Submodule K (MvPolynomial (σ ⊕ δ) K)) (F : MvPolynomial (σ ⊕ δ) K)
    (hsym : ∀ e : Equiv.Perm σ, rename (Equiv.sumCongr e (Equiv.refl δ)) F = F)
    (hF : F ∈ residualFiltration (τ := τ) U (shape f)) :
    (X (Sum.inl u) - X (Sum.inl v) : MvPolynomial (τ ⊕ δ) K) ^
      (2 * min (blockSize f u) (blockSize f v)) ∣ residualEval f F := by
  have hd := difference_pow_two_min_dvd f u v huv ⊤ (sumToIter K σ δ F)
    (sumToIter_isSymmetric F hsym) (sumToIter_mem_filtration U (shape f) F hF)
  rw [← sumToIter_residualEval] at hd
  have h := map_dvd (iterToSum K τ δ) hd
  simpa only [map_pow, map_sub, iterToSum_X, iterToSum_sumToIter] using h

end
end VOA.GordonResidualFiltration
