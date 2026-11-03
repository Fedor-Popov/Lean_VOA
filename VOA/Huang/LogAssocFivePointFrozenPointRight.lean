import VOA.Huang.LogAssocFivePointFunctionals
import VOA.Modules.LogTensorPzPointPrecompose

/-! A true outer logarithmic point block with its first input frozen gives
a genuinely supported functional on the second actual generalized module. -/
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

/-- Literal finite point-block pairing, linear on the actual second module. -/
noncomputable def frozenRightPointFunctional (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ) (x : M₁) :
    M₂ →ₗ[ℂ] ℂ :=
  f ∘ₗ (Complex.exp (ell*(c-a-b)) •
    ∑ k∈Finset.range (pointLogCutoff N₁ N₂ N₃ a b c),
      ell^k • (Y.1 (a+b-c-1) k) x)

/-- The right-input functional is exactly the actual chosen-branch block pairing. -/
theorem frozenRightPointFunctional_apply (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ)
    (x : N₁.weight a) (z : N₂.weight b) :
    frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f x z=
      f (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x z) := by
  simp only [frozenRightPointFunctional,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,LinearMap.flip_apply,pointEvaluationBlock,
    Submodule.coe_smul,Submodule.coe_sum]
  rfl

/-- Supported output tests produce truly supported right-input frozen
point functionals with every genuine logarithmic coefficient retained. -/
theorem frozenRightPointFunctional_supported (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ)
    (hf : SupportedAt N₃ f c) {x : M₁} (hx : x∈N₁.weight a) :
    SupportedAt N₂ (frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f x) b := by
  intro t ht z hz
  simp only [frozenRightPointFunctional,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,map_smul,map_sum]
  have hh (k : ℕ) : f (Y.1 (a+b-c-1) k x z)=0 := by
    apply hf (a+t-(a+b-c-1)-1)
    · intro he
      apply ht
      linear_combination he
    · exact Y.2.mem_weight hx hz _ k
  simp only [hh,smul_zero,Finset.sum_const_zero]

variable {X₁ X₂ : Type u} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]

/-- The true right-input frozen point functional commutes with actual
source maps, including all Jordan and logarithmic degrees. -/
theorem frozenRightPointFunctional_precompose (Q₁ : LogVModule W X₁) (Q₂ : LogVModule W X₂)
    (g₁ : Q₁.toWeakModule.Hom N₁.toWeakModule) (g₂ : Q₂.toWeakModule.Hom N₂.toWeakModule)
    (ell a b c : ℂ) (f : M₃ →ₗ[ℂ] ℂ) (hf : SupportedAt N₃ f c)
    {x : X₁} (hx : x∈Q₁.weight a) :
    frozenRightPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f x=
      frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f (g₁.toLinearMap x) ∘ₗ g₂.toLinearMap := by
  let A := frozenRightPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f x
  let B := frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f (g₁.toLinearMap x) ∘ₗ g₂.toLinearMap
  apply LinearMap.ext
  intro z
  change A z=B z
  refine LogFin.induction_on Q₂ (C := fun z => A z=B z) z ?_ (by simp [A,B]) ?_
  · intro t z hz
    by_cases htb : t=b
    · subst t
      change frozenRightPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f x z=
        frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f (g₁.toLinearMap x) (g₂.toLinearMap z)
      rw [frozenRightPointFunctional_apply Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f ⟨x,hx⟩ ⟨z,hz⟩,
        frozenRightPointFunctional_apply N₁ N₂ N₃ Y ell a b c f
          ⟨g₁.toLinearMap x,hom_mem_weight Q₁ N₁ g₁ hx⟩
          ⟨g₂.toLinearMap z,hom_mem_weight Q₂ N₂ g₂ hz⟩]
      congr 1
      exact pointEvaluationBlock_precompose N₁ N₂ N₃ Q₁ Q₂ g₁ g₂ Y ell a b c ⟨x,hx⟩ ⟨z,hz⟩
    · change frozenRightPointFunctional Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f x z=
        frozenRightPointFunctional N₁ N₂ N₃ Y ell a b c f (g₁.toLinearMap x) (g₂.toLinearMap z)
      rw [frozenRightPointFunctional_supported Q₁ Q₂ N₃ (precompose g₁ g₂ Y) ell a b c f hf hx t htb z hz,
        frozenRightPointFunctional_supported N₁ N₂ N₃ Y ell a b c f hf
          (hom_mem_weight Q₁ N₁ g₁ hx) t htb _ (hom_mem_weight Q₂ N₂ g₂ hz)]
  · intro z w hz hw
    rw [map_add,map_add,hz,hw]

end VOA.Huang.LogAssocFivePointFunctionals
