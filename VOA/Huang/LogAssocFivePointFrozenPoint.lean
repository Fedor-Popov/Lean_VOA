import VOA.Huang.LogAssocFivePointFunctionals
import VOA.Modules.LogTensorPzPointPrecompose

/-! A true outer logarithmic point block, with its second input and output
weight frozen, is a genuinely supported scalar functional on the first
actual generalized module. All logarithmic coefficients remain in the sum. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePointFunctionals
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficientCompatibility
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- Literal finite point-block pairing, extended linearly to the actual first module. -/
noncomputable def frozenPointFunctional (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ) (z : M₂) :
    M₁ →ₗ[ℂ] ℂ :=
  f ∘ₗ (Complex.exp (ell*(c-a-b)) •
    ∑ k∈Finset.range (pointLogCutoff N₁ N₂ N₃ a b c),
      ell^k • (Y.1 (a+b-c-1) k).flip z)

/-- On the true first-input weight, the frozen functional is exactly the
actual chosen-branch block pairing. -/
theorem frozenPointFunctional_apply (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ)
    (x : N₁.weight a) (z : N₂.weight b) :
    frozenPointFunctional N₁ N₂ N₃ Y ell a b c f z x=
      f (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x z) := by
  simp only [frozenPointFunctional,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,LinearMap.flip_apply,pointEvaluationBlock,
    Submodule.coe_smul,Submodule.coe_sum]
  rfl

/-- Supported output tests produce truly supported frozen point-block
functionals, independently of C2, finite generation, or semisimplicity. -/
theorem frozenPointFunctional_supported (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ)
    (hf : SupportedAt N₃ f c) {z : M₂} (hz : z∈N₂.weight b) :
    SupportedAt N₁ (frozenPointFunctional N₁ N₂ N₃ Y ell a b c f z) a := by
  intro s hs x hx
  simp only [frozenPointFunctional,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,LinearMap.flip_apply,map_smul,map_sum]
  have hh (k : ℕ) : f (Y.1 (a+b-c-1) k x z)=0 := by
    apply hf (s+b-(a+b-c-1)-1)
    · intro he
      apply hs
      linear_combination he
    · exact Y.2.mem_weight hx hz _ k
  simp only [hh,smul_zero,Finset.sum_const_zero]


variable {X₁ X₂ : Type u} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]

/-- Actual input morphisms commute with the genuinely supported frozen
point functional, even when the true finite logarithmic cutoffs change. -/
theorem frozenPointFunctional_precompose (Q₁ : LogVModule W X₁) (Q₂ : LogVModule W X₂)
    (g₁ : Q₁.toWeakModule.Hom N₁.toWeakModule) (g₂ : Q₂.toWeakModule.Hom N₂.toWeakModule)
    (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ) (hf : SupportedAt N₃ f c)
    {z : X₂} (hz : z∈Q₂.weight b) :
    frozenPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f z=
      frozenPointFunctional N₁ N₂ N₃ Y ell a b c f (g₂.toLinearMap z) ∘ₗ g₁.toLinearMap := by
  let A := frozenPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f z
  let B := frozenPointFunctional N₁ N₂ N₃ Y ell a b c f (g₂.toLinearMap z) ∘ₗ g₁.toLinearMap
  apply LinearMap.ext
  intro x
  change A x=B x
  refine LogFin.induction_on Q₁ (C := fun x => A x=B x) x ?_ (by simp [A,B]) ?_
  · intro t x hx
    by_cases hta : t=a
    · subst t
      change frozenPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f z x=
        frozenPointFunctional N₁ N₂ N₃ Y ell a b c f (g₂.toLinearMap z) (g₁.toLinearMap x)
      rw [frozenPointFunctional_apply Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f ⟨x,hx⟩ ⟨z,hz⟩,
        frozenPointFunctional_apply N₁ N₂ N₃ Y ell a b c f
          ⟨g₁.toLinearMap x,hom_mem_weight Q₁ N₁ g₁ hx⟩
          ⟨g₂.toLinearMap z,hom_mem_weight Q₂ N₂ g₂ hz⟩]
      congr 1
      exact pointEvaluationBlock_precompose N₁ N₂ N₃ Q₁ Q₂ g₁ g₂ Y ell a b c ⟨x,hx⟩ ⟨z,hz⟩
    · change frozenPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f z x=
        frozenPointFunctional N₁ N₂ N₃ Y ell a b c f (g₂.toLinearMap z) (g₁.toLinearMap x)
      rw [frozenPointFunctional_supported Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f hf hz t hta x hx,
        frozenPointFunctional_supported N₁ N₂ N₃ Y ell a b c f hf
          (hom_mem_weight Q₂ N₂ g₂ hz) t hta _ (hom_mem_weight Q₁ N₁ g₁ hx)]
  · intro x y hx hy
    rw [map_add,map_add,hx,hy]

end VOA.Huang.LogAssocFivePointFunctionals
