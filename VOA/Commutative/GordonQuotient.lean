/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonSymmetry
import VOA.Commutative.MvPolynomialFiniteHomogeneous

/-! # The divided Gordon quotient and its invariant polynomial injection -/

namespace VOA.GordonQuotient

open VOA.GordonFiltration VOA.GordonDivisor VOA.GordonSymmetry

noncomputable section

variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [LinearOrder τ]
variable [Field K] [CharZero K]

/-- Polynomials symmetric among every family of equally sized blocks. -/
def invariantSubmodule (f : σ → τ) : Submodule K (MvPolynomial τ K) where
  carrier := {q | ∀ e : Equiv.Perm τ, (∀ j, blockSize f (e j) = blockSize f j) →
    MvPolynomial.rename e q = q}
  zero_mem' := by intro e _; exact map_zero (MvPolynomial.rename e)
  add_mem' := by intro p q hp hq e he; simp only [map_add, hp e he, hq e he]
  smul_mem' := by intro c p hp e he; simp only [map_smul, hp e he]

/-- Every element in the evaluated filtration image has an invariant polynomial quotient. -/
theorem image_exists_quotient (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (x : (restrictedEval U f).range) :
    ∃ q : invariantSubmodule (K := K) f, (x : MvPolynomial τ K) = clusterDivisor f * (q : MvPolynomial τ K) := by
  obtain ⟨F, hF⟩ := x.property
  have hs := hU F.val ((mem_filtration U (shape f) F.val).mp F.property).1
  obtain ⟨q, hq, hi⟩ := exists_symmetric_quotient f U F.val hs F.property
  refine ⟨⟨q, hi⟩, ?_⟩
  rw [← hF]
  exact hq

/-- Divide the actual evaluation image by the nonzero cluster divisor. -/
def dividedImage (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) :
    (restrictedEval U f).range →ₗ[K] invariantSubmodule (K := K) f where
  toFun x := (image_exists_quotient f U hU x).choose
  map_add' x y := by
    apply Subtype.ext
    apply mul_left_cancel₀ (clusterDivisor_ne_zero (K := K) f)
    simp only [Submodule.coe_add]
    rw [mul_add, ← (image_exists_quotient f U hU (x + y)).choose_spec,
      ← (image_exists_quotient f U hU x).choose_spec,
      ← (image_exists_quotient f U hU y).choose_spec]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    apply mul_left_cancel₀ (clusterDivisor_ne_zero (K := K) f)
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [mul_smul_comm, ← (image_exists_quotient f U hU (c • x)).choose_spec,
      ← (image_exists_quotient f U hU x).choose_spec]
    rfl

theorem dividedImage_spec (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) (x : (restrictedEval U f).range) :
    (x : MvPolynomial τ K) = clusterDivisor f * (dividedImage f U hU x : MvPolynomial τ K) :=
  (image_exists_quotient f U hU x).choose_spec

theorem dividedImage_injective (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) : Function.Injective (dividedImage f U hU) := by
  intro x y hxy
  apply Subtype.ext
  rw [dividedImage_spec f U hU x, dividedImage_spec f U hU y, hxy]

/-- The actual Gordon successive quotient maps linearly into its separately
symmetric divided polynomial ring. -/
def quotientInjection (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) :
    ((filtration (τ := τ) U (shape f)) ⧸ (restrictedEval U f).ker) →ₗ[K]
      invariantSubmodule (K := K) f :=
  (dividedImage f U hU).comp (quotientEquivImage U f).toLinearMap

theorem quotientInjection_injective (f : σ → τ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ F ∈ U, F.IsSymmetric) : Function.Injective (quotientInjection f U hU) :=
  (dividedImage_injective f U hU).comp (quotientEquivImage U f).injective

end
end VOA.GordonQuotient
