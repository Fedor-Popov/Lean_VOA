/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocConverseChannels

/-!
# Finite channel families and the remaining independence problem

Completeness of a finite irreducible family gives the iterate dimension upper bound.
The separate product evaluation injectivity condition is the remaining independence
problem. Neither completeness nor independence asserts any associativity identity.
-/

namespace VOA.Huang.AssocConverse

open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget VOA.Huang.FusionUnit Module
open scoped BigOperators TensorProduct

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ P₃ P₄ : LWModule W}

/-- Transport an iterate through an isomorphism of the intermediate module. -/
noncomputable def IterateChannel.transport (C : IterateChannel P₁ P₂ P₃ P₄)
    (R : LWModule W) (iR : R.IsIrreducibleLW) (e : ModuleEquiv W C.Q.isMod R.isMod) :
    IterateChannel P₁ P₂ P₃ P₄ :=
  ⟨R, iR,
    ⟨fun n => (C.outer.val n).comp e.symm.toLinearEquiv.toLinearMap,
      isIntertwiningOperator_precomp C.outer.property (fun a n x => e.symm.map_act a n x)⟩,
    ⟨fun n => (C.inner.val n).compr₂ e.toLinearEquiv.toLinearMap,
      isIntertwiningOperator_compHom C.inner.property (fun a n x => e.map_act a n x)⟩⟩

theorem IterateChannel.eval_transport (C : IterateChannel P₁ P₂ P₃ P₄)
    (R : LWModule W) (iR : R.IsIrreducibleLW) (e : ModuleEquiv W C.Q.isMod R.isMod) :
    (C.transport R iR e).eval = C.eval := by
  funext d
  have hh := LWModule.h_eq_of_iso W e
  unfold IterateChannel.eval iterValue
  simp only [IterateChannel.transport, ← hh]
  apply tsum_congr
  intro k
  congr 2
  change d.f (C.outer.val _ (e.symm.toLinearEquiv
    (e.toLinearEquiv (C.inner.val _ d.w₁ d.w₂))) d.w₃) = _
  change d.f (C.outer.val _ (e.toLinearEquiv.symm
    (e.toLinearEquiv (C.inner.val _ d.w₁ d.w₂))) d.w₃) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Sum of a finite family of linear maps with different domains. -/
noncomputable def sumFamily {ι : Type v} [Fintype ι] {E : ι → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {F : Type*} [AddCommGroup F] [Module ℂ F] (L : ∀ j, E j →ₗ[ℂ] F) :
    (∀ j, E j) →ₗ[ℂ] F where
  toFun x := ∑ j, L j (x j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum]

theorem mem_range_sumFamily {ι : Type v} [Fintype ι] {E : ι → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {F : Type*} [AddCommGroup F] [Module ℂ F] (L : ∀ j, E j →ₗ[ℂ] F) (j : ι) (x : E j) :
    L j x ∈ LinearMap.range (sumFamily L) := by
  classical
  refine ⟨Pi.single j x, ?_⟩
  change (∑ k, L k (Pi.single j x k)) = L j x
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · simp

variable {ι : Type v} [Fintype ι]

noncomputable def productFamilyMap (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (R : ι → LWModule W) :
    (∀ j, productTensor P₁ P₂ P₃ P₄ (R j)) →ₗ[ℂ] (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  sumFamily fun j => productTensorMap hV i₁ i₂ i₃ i₄ (R j)

noncomputable def iterateFamilyMap (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (R : ι → LWModule W) :
    (∀ j, iterateTensor P₁ P₂ P₃ P₄ (R j)) →ₗ[ℂ] (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  sumFamily fun j => iterateTensorMap hV i₁ i₂ i₃ i₄ (R j)

theorem productFamilyMap_range_le (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW) :
    LinearMap.range (productFamilyMap hV i₁ i₂ i₃ i₄ R) ≤ productSpan P₁ P₂ P₃ P₄ := by
  rintro _ ⟨z, rfl⟩
  exact Submodule.sum_mem _ fun j _ =>
    productTensorMap_range_le hV i₁ i₂ i₃ i₄ (iR j) ⟨z j, rfl⟩

theorem iterateFamilyMap_range_le (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW) :
    LinearMap.range (iterateFamilyMap hV i₁ i₂ i₃ i₄ R) ≤ iterateSpan P₁ P₂ P₃ P₄ := by
  rintro _ ⟨z, rfl⟩
  exact Submodule.sum_mem _ fun j _ =>
    iterateTensorMap_range_le hV i₁ i₂ i₃ i₄ (iR j) ⟨z j, rfl⟩

/-- Completeness supplies spanning, without any independence or converse hypothesis. -/
theorem iterateFamilyMap_range_eq (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j)) :
    LinearMap.range (iterateFamilyMap hV i₁ i₂ i₃ i₄ R) = iterateSpan P₁ P₂ P₃ P₄ := by
  apply le_antisymm (iterateFamilyMap_range_le hV i₁ i₂ i₃ i₄ R iR)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨C, rfl⟩
  obtain ⟨j, ⟨e⟩⟩ := hcomplete C.Q C.irreducible
  rw [← C.eval_transport (R j) (iR j) e]
  exact mem_range_sumFamily (fun j => iterateTensorMap hV i₁ i₂ i₃ i₄ (R j)) j
    ((C.transport (R j) (iR j) e).outer ⊗ₜ[ℂ] (C.transport (R j) (iR j) e).inner)

theorem finrank_productFamily (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW) :
    finrank ℂ (∀ j, productTensor P₁ P₂ P₃ P₄ (R j)) = productMultiplicity R P₁ P₂ P₃ P₄ := by
  letI (j : ι) := finiteDimensional_productTensor hV i₁ i₂ i₃ i₄ (iR j)
  letI (j : ι) : Module.Free ℂ (productTensor P₁ P₂ P₃ P₄ (R j)) :=
    Module.Free.of_divisionRing ℂ _
  rw [Module.finrank_pi_fintype]
  unfold productMultiplicity
  apply Finset.sum_congr rfl
  intro j _
  exact Module.finrank_tensorProduct

theorem finrank_iterateFamily (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW) :
    finrank ℂ (∀ j, iterateTensor P₁ P₂ P₃ P₄ (R j)) = iterateMultiplicity R P₁ P₂ P₃ P₄ := by
  letI (j : ι) := finiteDimensional_iterateTensor hV i₁ i₂ i₃ i₄ (iR j)
  letI (j : ι) : Module.Free ℂ (iterateTensor P₁ P₂ P₃ P₄ (R j)) :=
    Module.Free.of_divisionRing ℂ _
  rw [Module.finrank_pi_fintype]
  unfold iterateMultiplicity
  apply Finset.sum_congr rfl
  intro j _
  exact Module.finrank_tensorProduct

/-- The iterate upper bound is proved from a complete finite family and strong rationality. -/
theorem iterateDimensionUpperBound_of_complete (hV : StronglyRational W)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j)) :
    IterateDimensionUpperBound R := by
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  letI (j : ι) := finiteDimensional_iterateTensor hV i₁ i₂ i₃ i₄ (iR j)
  rw [← iterateFamilyMap_range_eq hV i₁ i₂ i₃ i₄ R iR hcomplete]
  refine ⟨inferInstance, ?_⟩
  exact (LinearMap.finrank_range_le _).trans_eq (finrank_iterateFamily hV i₁ i₂ i₃ i₄ R iR)

/-- Independence of actual product evaluations. Intended for an irredundant irreducible
family; it is not asserted for families with repeated isomorphism classes. -/
def ProductChannelFaithful (hV : StronglyRational W) (R : ι → LWModule W) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W) (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW),
    Function.Injective (productFamilyMap hV i₁ i₂ i₃ i₄ R)

theorem productDimensionLowerBound_of_faithful (hV : StronglyRational W)
    (hassoc : AssociativityInput W) (R : ι → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW) (hupper : IterateDimensionUpperBound R)
    (hfaith : ProductChannelFaithful hV R) : ProductDimensionLowerBound R := by
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  letI := (hupper P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄).1
  letI : FiniteDimensional ℂ (productSpan P₁ P₂ P₃ P₄) :=
    Submodule.finiteDimensional_of_le (productSpan_le_iterateSpan hassoc i₁ i₂ i₃ i₄)
  rw [← finrank_productFamily hV i₁ i₂ i₃ i₄ R iR,
    ← LinearMap.finrank_range_of_inj (hfaith P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄)]
  exact Submodule.finrank_mono (productFamilyMap_range_le hV i₁ i₂ i₃ i₄ R iR)

/-- All remaining content of this route is product-channel independence. -/
theorem associativityConverse_of_productChannelFaithful (hV : StronglyRational W)
    (hassoc : AssociativityInput W) (R : ι → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j))
    (hfaith : ProductChannelFaithful hV R) : AssociativityConverse W := by
  have hupper := iterateDimensionUpperBound_of_complete hV R iR hcomplete
  exact associativityConverse_of_dimension_bounds hassoc R
    (productDimensionLowerBound_of_faithful hV hassoc R iR hupper hfaith) hupper

end VOA.Huang.AssocConverse
