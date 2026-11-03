/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonQuotient

/-! # The graded Gordon quotient injection and coefficientwise dimension bound -/

namespace VOA.GordonGradedQuotient

open VOA.GordonFiltration VOA.GordonDivisor VOA.GordonQuotient

noncomputable section

variable {K I : Type*} [Field K]

/-- Multiplication by a weighted-homogeneous left factor commutes with extracting the component
whose degree is the sum of the factor degree and the requested residual degree. -/
theorem weightedHomogeneousComponent_mul_left
    (w : I → ℕ) {C q : MvPolynomial I K} {c r : ℕ}
    (hC : C.IsWeightedHomogeneous w c) :
    MvPolynomial.weightedHomogeneousComponent w (c + r) (C * q) =
      C * MvPolynomial.weightedHomogeneousComponent w r q := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule K w) :=
    MvPolynomial.weightedGradedAlgebra K w
  have h :=
    (DirectSum.coe_decompose_mul_add_of_left_mem
      (MvPolynomial.weightedHomogeneousSubmodule K w) hC :
      ((DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) (C * q)
        (c + r) : MvPolynomial I K) =
        C * DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) q r))
  change
    (((MvPolynomial.weightedDecomposition K w).decompose' (C * q) (c + r) :
        MvPolynomial I K) =
      C * ((MvPolynomial.weightedDecomposition K w).decompose' q r :
        MvPolynomial I K)) at h
  simpa only [MvPolynomial.weightedDecomposition.decompose'_apply] using h

/-- A nonzero weighted-homogeneous factor can be cancelled from a weighted-homogeneous product;
the quotient has the residual weighted degree. -/
theorem quotient_weightedHomogeneous_of_factorization
    (w : I → ℕ) (C p q : MvPolynomial I K) (c r : ℕ)
    (hC0 : C ≠ 0) (hC : C.IsWeightedHomogeneous w c)
    (hp : p.IsWeightedHomogeneous w (c + r)) (hfac : p = C * q) :
    q.IsWeightedHomogeneous w r := by
  intro d hd
  by_contra hdegree
  have hcomponentQ :
      MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w d) q ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff d) hzero
    simp [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
    exact hd hcoeff
  have hcomponentProduct :
      MvPolynomial.weightedHomogeneousComponent w
          (c + Finsupp.weight w d) (C * q) ≠ 0 := by
    rw [weightedHomogeneousComponent_mul_left w hC]
    exact mul_ne_zero hC0 hcomponentQ
  have hne : c + Finsupp.weight w d ≠ c + r :=
    Nat.add_left_cancel_iff.not.mpr hdegree
  have hzero :
      MvPolynomial.weightedHomogeneousComponent w
          (c + Finsupp.weight w d) p = 0 :=
    hp.weightedHomogeneousComponent_ne (c + Finsupp.weight w d) hne
  rw [hfac] at hzero
  exact hcomponentProduct hzero


variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [LinearOrder τ]
variable [CharZero K]

/-- The homogeneous degree-`r` separately symmetric target space. -/
def invariantPiece (f : σ → τ) (r : ℕ) : Submodule K (MvPolynomial τ K) :=
  invariantSubmodule (K := K) f ⊓ MvPolynomial.homogeneousSubmodule τ K r

instance invariantPiece_finite (f : σ → τ) (r : ℕ) :
    FiniteDimensional K (invariantPiece (K := K) f r) := by
  letI := VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_homogeneousSubmodule
    (K := K) (I := τ) r
  exact FiniteDimensional.of_injective (Submodule.inclusion (show invariantPiece (K := K) f r ≤
    MvPolynomial.homogeneousSubmodule τ K r from inf_le_right))
    (Submodule.inclusion_injective _)

/-- Dividing by the homogeneous cluster divisor lowers polynomial degree by exactly
its degree, for the actual evaluated filtration image. -/
theorem dividedImage_isHomogeneous (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r))
    (x : (restrictedEval U f).range) :
    (dividedImage f U hU x : MvPolynomial τ K).IsHomogeneous r := by
  apply quotient_weightedHomogeneous_of_factorization 1 (clusterDivisor f) x.val
    (dividedImage f U hU x) (clusterDegree f) r (clusterDivisor_ne_zero f)
    (clusterDivisor_isHomogeneous f)
  · obtain ⟨F, hF⟩ := x.property
    rw [← hF]
    exact (hdegree F.val ((mem_filtration U (shape f) F.val).mp F.property).1).rename_isHomogeneous
  · exact dividedImage_spec f U hU x

/-- The divided evaluation image lands in the correct homogeneous invariant piece. -/
def gradedImageMap (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r)) :
    (restrictedEval U f).range →ₗ[K] invariantPiece (K := K) f r :=
  ((invariantSubmodule (K := K) f).subtype.comp (dividedImage f U hU)).codRestrict
    (invariantPiece (K := K) f r) (fun x ↦ ⟨(dividedImage f U hU x).property,
      dividedImage_isHomogeneous f U hU r hdegree x⟩)

theorem gradedImageMap_injective (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r)) :
    Function.Injective (gradedImageMap f U hU r hdegree) := by
  intro x y hxy
  apply dividedImage_injective f U hU
  apply Subtype.ext
  exact congrArg (fun q : invariantPiece (K := K) f r ↦ (q : MvPolynomial τ K)) hxy

/-- The degree-shifted injection for the actual successive Gordon quotient. -/
def gradedQuotientInjection (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r)) :
    ((filtration (τ := τ) U (shape f)) ⧸ (restrictedEval U f).ker) →ₗ[K]
      invariantPiece (K := K) f r :=
  (gradedImageMap f U hU r hdegree).comp (quotientEquivImage U f).toLinearMap

theorem gradedQuotientInjection_injective (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r)) :
    Function.Injective (gradedQuotientInjection f U hU r hdegree) :=
  (gradedImageMap_injective f U hU r hdegree).comp (quotientEquivImage U f).injective

/-- Coefficientwise Hilbert bound supplied by the cluster divisor and equal-size symmetry. -/
theorem finrank_quotient_le_invariantPiece (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (r : ℕ)
    (hdegree : ∀ F ∈ U, F.IsHomogeneous (clusterDegree f + r)) :
    Module.finrank K ((filtration (τ := τ) U (shape f)) ⧸ (restrictedEval U f).ker) ≤
      Module.finrank K (invariantPiece (K := K) f r) :=
  LinearMap.finrank_le_finrank_of_injective
    (gradedQuotientInjection_injective f U hU r hdegree)

end
end VOA.GordonGradedQuotient
