/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocConverseRank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Evaluation of finite families of tensor channels

The evaluation maps take tensors of actual intertwining operators to simultaneous
matrix-coefficient functions. Linearity of evaluation uses the proved absolute
convergence, not a formal interchange of divergent sums.
-/

namespace VOA.Huang.AssocConverse

open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget Module
open scoped BigOperators TensorProduct

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ P₃ P₄ Q : LWModule W}

noncomputable def productTerm
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) : ℂ :=
  let σ := d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2
  let ν := d.α₂ + d.α₃ - 1 - Q.h
  prodCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃ (σ - ν + k) (ν - k)
    * (1 + (d.x : ℂ)) ^ (-(σ - ν + k) - 1) * (1 : ℂ) ^ (-(ν - k) - 1)

noncomputable def productValue
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) : ℂ := ∑' k, productTerm A B d k

theorem productTerm_add_left
    (A A' : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    productTerm (A + A') (B) d k = productTerm A B d k + productTerm A' B d k := by
  change prodCoeff (A.val + A'.val)
    (B.val) _ _ _ _ _ _ * _ * _ = _
  rw [prodCoeff_add_left]
  unfold productTerm
  ring

theorem productTerm_smul_left
    (a : ℂ) (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    productTerm (a • A) (B) d k = a * productTerm A B d k := by
  change prodCoeff (a • A.val)
    (B.val) _ _ _ _ _ _ * _ * _ = _
  rw [prodCoeff_smul_left]
  unfold productTerm
  ring

theorem productTerm_add_right
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B B' : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    productTerm (A) (B + B') d k = productTerm A B d k + productTerm A B' d k := by
  change prodCoeff (A.val)
    (B.val + B'.val) _ _ _ _ _ _ * _ * _ = _
  rw [prodCoeff_add_right]
  unfold productTerm
  ring

theorem productTerm_smul_right
    (a : ℂ) (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    productTerm (A) (a • B) d k = a * productTerm A B d k := by
  change prodCoeff (A.val)
    (a • B.val) _ _ _ _ _ _ * _ * _ = _
  rw [prodCoeff_smul_right]
  unfold productTerm
  ring

theorem summable_productTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (productTerm A B d) := by
  apply summable_prodValue hV i₁ i₂ i₃ i₄ A.property B.property
    d.hw₁ d.hw₂ d.hw₃ d.hf (z₁ := 1 + (d.x : ℂ)) (z₂ := 1)
  · simp
  · rw [show 1 + (d.x : ℂ) = ((1 + d.x : ℝ) : ℂ) by push_cast; rfl,
      norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [d.xpos])]
    linarith [d.xpos]

noncomputable def productBilinear (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (Q : LWModule W) :
    IntertwiningOperator P₁.isMod Q.isMod P₄.isMod →ₗ[ℂ]
      IntertwiningOperator P₂.isMod P₃.isMod Q.isMod →ₗ[ℂ]
        (TestData P₁ P₂ P₃ P₄ → ℂ) where
  toFun A :=
    { toFun := productValue A
      map_add' := by
        intro B B'
        funext d
        simp only [productValue, productTerm_add_right, Pi.add_apply]
        exact (summable_productTerm hV i₁ i₂ i₃ i₄ A B d).tsum_add
          (summable_productTerm hV i₁ i₂ i₃ i₄ A B' d)
      map_smul' := by
        intro a B
        funext d
        simp only [productValue, productTerm_smul_right, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        rw [tsum_mul_left] }
  map_add' := by
    intro A A'
    ext B d
    change (∑' k, productTerm (A + A') B d k) =
      (∑' k, productTerm A B d k) + ∑' k, productTerm A' B d k
    simp only [productTerm_add_left]
    exact (summable_productTerm hV i₁ i₂ i₃ i₄ A B d).tsum_add
      (summable_productTerm hV i₁ i₂ i₃ i₄ A' B d)
  map_smul' := by
    intro a A
    ext B d
    change (∑' k, productTerm (a • A) B d k) = a * ∑' k, productTerm A B d k
    simp only [productTerm_smul_left]
    rw [tsum_mul_left]

abbrev productTensor (P₁ P₂ P₃ P₄ Q : LWModule W) :=
  (IntertwiningOperator P₁.isMod Q.isMod P₄.isMod) ⊗[ℂ]
    (IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)

noncomputable def productTensorMap (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (Q : LWModule W) :
    productTensor P₁ P₂ P₃ P₄ Q →ₗ[ℂ] (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  TensorProduct.lift (productBilinear hV i₁ i₂ i₃ i₄ Q)

noncomputable def iterateTerm
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) : ℂ :=
  let σ := d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2
  let ν := d.α₁ + d.α₂ - 1 - Q.h
  iterCoeff A.val B.val d.f d.w₁ d.w₂ d.w₃ (ν - k) (σ - ν + k)
    * (1 : ℂ) ^ (-(σ - ν + k) - 1) * (d.x : ℂ) ^ (-(ν - k) - 1)

noncomputable def iterateValue
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) : ℂ := ∑' k, iterateTerm A B d k

theorem iterateTerm_add_left
    (A A' : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    iterateTerm (A + A') (B) d k = iterateTerm A B d k + iterateTerm A' B d k := by
  change iterCoeff (A.val + A'.val)
    (B.val) _ _ _ _ _ _ * _ * _ = _
  rw [iterCoeff_add_left]
  unfold iterateTerm
  ring

theorem iterateTerm_smul_left
    (a : ℂ) (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    iterateTerm (a • A) (B) d k = a * iterateTerm A B d k := by
  change iterCoeff (a • A.val)
    (B.val) _ _ _ _ _ _ * _ * _ = _
  rw [iterCoeff_smul_left]
  unfold iterateTerm
  ring

theorem iterateTerm_add_right
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B B' : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    iterateTerm (A) (B + B') d k = iterateTerm A B d k + iterateTerm A B' d k := by
  change iterCoeff (A.val)
    (B.val + B'.val) _ _ _ _ _ _ * _ * _ = _
  rw [iterCoeff_add_right]
  unfold iterateTerm
  ring

theorem iterateTerm_smul_right
    (a : ℂ) (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (k : ℕ) :
    iterateTerm (A) (a • B) d k = a * iterateTerm A B d k := by
  change iterCoeff (A.val)
    (a • B.val) _ _ _ _ _ _ * _ * _ = _
  rw [iterCoeff_smul_right]
  unfold iterateTerm
  ring

theorem summable_iterateTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (iterateTerm A B d) := by
  apply summable_iterValue hV i₁ i₂ i₃ i₄ A.property B.property
    d.hw₁ d.hw₂ d.hw₃ d.hf (z₀ := (d.x : ℂ)) (z₂ := 1)
  · exact_mod_cast d.xpos.ne'
  · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.xpos] using d.xlt

noncomputable def iterateBilinear (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (Q : LWModule W) :
    IntertwiningOperator Q.isMod P₃.isMod P₄.isMod →ₗ[ℂ]
      IntertwiningOperator P₁.isMod P₂.isMod Q.isMod →ₗ[ℂ]
        (TestData P₁ P₂ P₃ P₄ → ℂ) where
  toFun A :=
    { toFun := iterateValue A
      map_add' := by
        intro B B'
        funext d
        simp only [iterateValue, iterateTerm_add_right, Pi.add_apply]
        exact (summable_iterateTerm hV i₁ i₂ i₃ i₄ A B d).tsum_add
          (summable_iterateTerm hV i₁ i₂ i₃ i₄ A B' d)
      map_smul' := by
        intro a B
        funext d
        simp only [iterateValue, iterateTerm_smul_right, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        rw [tsum_mul_left] }
  map_add' := by
    intro A A'
    ext B d
    change (∑' k, iterateTerm (A + A') B d k) =
      (∑' k, iterateTerm A B d k) + ∑' k, iterateTerm A' B d k
    simp only [iterateTerm_add_left]
    exact (summable_iterateTerm hV i₁ i₂ i₃ i₄ A B d).tsum_add
      (summable_iterateTerm hV i₁ i₂ i₃ i₄ A' B d)
  map_smul' := by
    intro a A
    ext B d
    change (∑' k, iterateTerm (a • A) B d k) = a * ∑' k, iterateTerm A B d k
    simp only [iterateTerm_smul_left]
    rw [tsum_mul_left]

abbrev iterateTensor (P₁ P₂ P₃ P₄ Q : LWModule W) :=
  (IntertwiningOperator Q.isMod P₃.isMod P₄.isMod) ⊗[ℂ]
    (IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)

noncomputable def iterateTensorMap (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (Q : LWModule W) :
    iterateTensor P₁ P₂ P₃ P₄ Q →ₗ[ℂ] (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  TensorProduct.lift (iterateBilinear hV i₁ i₂ i₃ i₄ Q)


/-- Evaluated tensors lie in the span of actual channels. -/
theorem productTensorMap_range_le (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW) :
    LinearMap.range (productTensorMap hV i₁ i₂ i₃ i₄ Q) ≤ productSpan P₁ P₂ P₃ P₄ := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul A B =>
    exact Submodule.subset_span ⟨(⟨Q, iQ, A, B⟩ : ProductChannel P₁ P₂ P₃ P₄), rfl⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem finiteDimensional_productTensor (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW) :
    FiniteDimensional ℂ (productTensor P₁ P₂ P₃ P₄ Q) := by
  letI := VOA.Huang.ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV i₁ iQ i₄
  letI := VOA.Huang.ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV i₂ i₃ iQ
  infer_instance


/-- Evaluated tensors lie in the span of actual channels. -/
theorem iterateTensorMap_range_le (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW) :
    LinearMap.range (iterateTensorMap hV i₁ i₂ i₃ i₄ Q) ≤ iterateSpan P₁ P₂ P₃ P₄ := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul A B =>
    exact Submodule.subset_span ⟨(⟨Q, iQ, A, B⟩ : IterateChannel P₁ P₂ P₃ P₄), rfl⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem finiteDimensional_iterateTensor (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW) :
    FiniteDimensional ℂ (iterateTensor P₁ P₂ P₃ P₄ Q) := by
  letI := VOA.Huang.ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV iQ i₃ i₄
  letI := VOA.Huang.ModuleC2.finiteDimensional_intertwiningSpace_of_stronglyRational hV i₁ i₂ iQ
  infer_instance

end VOA.Huang.AssocConverse
