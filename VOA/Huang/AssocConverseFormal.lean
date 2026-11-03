import VOA.Huang.AssocConverseCoefficients

/-! # Algebraic separation of products through one irreducible module

These maps retain both mode indices and all input vectors. No convergence or
analytic uniqueness is implicit in their definition.
-/

namespace VOA.Huang.AssocConverse
open VOA
open scoped BigOperators TensorProduct

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- A vanishing sum of coefficient products has zero left factors when the
right factors are independent and the intermediate module is irreducible. -/
theorem left_eq_zero_of_coefficient_products {ι : Type v} [Fintype ι]
    (iQ : Q.IsIrreducibleLW)
    (A : ι → IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : ι → IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (hB : LinearIndependent ℂ B)
    (hzero : ∀ p n x y z,
      ∑ j, (A j).val p x ((B j).val n y z) = 0) : ∀ j, A j = 0 := by
  classical
  intro j
  apply Subtype.ext
  funext p
  ext x z
  let L : (ι → Q.carrier) →ₗ[ℂ] P₄.carrier :=
    ∑ k, ((A k).val p x).comp (LinearMap.proj k)
  have hL : coefficientSpan B ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, y, w, rfl⟩
    change L (coefficientVector B n y w) = 0
    simpa [L, coefficientVector] using hzero p n x y w
  rw [coefficientSpan_eq_top iQ B hB] at hL
  have he : L (Pi.single j z) = 0 := hL (Submodule.mem_top)
  simpa [L, Pi.single_apply, apply_ite] using he

/-- All vector-valued product coefficients, with two independent mode indices. -/
abbrev FormalProductData (P₁ P₂ P₃ : LWModule W) :=
  ℂ × ℂ × P₁.carrier × P₂.carrier × P₃.carrier

noncomputable def formalProductBilinear (P₁ P₂ P₃ P₄ Q : LWModule W) :
    IntertwiningOperator P₁.isMod Q.isMod P₄.isMod →ₗ[ℂ]
      IntertwiningOperator P₂.isMod P₃.isMod Q.isMod →ₗ[ℂ]
        (FormalProductData P₁ P₂ P₃ → P₄.carrier) where
  toFun A :=
    { toFun := fun B d => A.val d.1 d.2.2.1 (B.val d.2.1 d.2.2.2.1 d.2.2.2.2)
      map_add' := by intros; funext d; simp
      map_smul' := by intros; funext d; simp }
  map_add' := by intros; ext B d; rfl
  map_smul' := by intros; ext B d; rfl

noncomputable def formalProductTensorMap (P₁ P₂ P₃ P₄ Q : LWModule W) :
    productTensor P₁ P₂ P₃ P₄ Q →ₗ[ℂ]
      (FormalProductData P₁ P₂ P₃ → P₄.carrier) :=
  TensorProduct.lift (formalProductBilinear P₁ P₂ P₃ P₄ Q)

@[simp] theorem formalProductTensorMap_tmul
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : FormalProductData P₁ P₂ P₃) :
    formalProductTensorMap P₁ P₂ P₃ P₄ Q (A ⊗ₜ[ℂ] B) d =
      A.val d.1 d.2.2.1 (B.val d.2.1 d.2.2.2.1 d.2.2.2.2) := rfl

/-- Formal products are faithful within one irreducible intermediate module.
Only finite tensor support is needed; the intertwiner spaces may be infinite. -/
theorem formalProductTensorMap_injective (iQ : Q.IsIrreducibleLW) :
    Function.Injective (formalProductTensorMap P₁ P₂ P₃ P₄ Q) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro t ht
  let b := Module.Basis.ofVectorSpace ℂ (IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b t
  let A : c.support → IntertwiningOperator P₁.isMod Q.isMod P₄.isMod := fun j => c j
  let B : c.support → IntertwiningOperator P₂.isMod P₃.isMod Q.isMod := fun j => b j
  have hB : LinearIndependent ℂ B := b.linearIndependent.comp _ Subtype.val_injective
  have hz : ∀ p n x y z, ∑ j, (A j).val p x ((B j).val n y z) = 0 := by
    intro p n x y z
    have he := congrFun ht (p, n, x, y, z)
    simp only [Finsupp.sum, map_sum, Finset.sum_apply,
      formalProductTensorMap_tmul, Pi.zero_apply] at he
    change (∑ j : c.support, (c j).val p x ((b j).val n y z)) = 0
    exact (Finset.sum_coe_sort c.support
      (fun j => (c j).val p x ((b j).val n y z))).trans he
  have hA := left_eq_zero_of_coefficient_products iQ A B hB hz
  apply Finset.sum_eq_zero
  intro j hj
  have hc : c j = 0 := hA ⟨j, hj⟩
  change c j ⊗ₜ[ℂ] b j = 0
  rw [hc, TensorProduct.zero_tmul]

end VOA.Huang.AssocConverse
