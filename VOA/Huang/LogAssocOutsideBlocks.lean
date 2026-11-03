import VOA.Huang.LogAssocOutsideLinearity
import VOA.Huang.LogAssocCoefficientCompatibility

/-! Actual homogeneous outside coefficient blocks, using projections of the
genuine generalized grading and the literal collision expansion coefficients. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open Module (Dual)
open VOA.Huang.LogAssocCoefficientCompatibility
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Extend a homogeneous dual vector by its actual generalized-weight projection. -/
noncomputable def extendedFunctional (N : LogVModule W M) (β : ℂ) :
    Dual ℂ (N.weight β) →ₗ[ℂ] Dual ℂ M where
  toFun g := g ∘ₗ internalProjTo N.isInternal β
  map_add' g h := LinearMap.add_comp _ _ _
  map_smul' s g := LinearMap.smul_comp _ _ _

theorem extendedFunctional_supported (N : LogVModule W M) (β : ℂ) (g : Dual ℂ (N.weight β)) :
    SupportedAt N (extendedFunctional N β g) β := by
  intro a ha x hx
  change g (internalProjTo N.isInternal β x)=0
  have he : internalProjTo N.isInternal β x=0 :=
    C2Rigid.internalProjTo_eq_zero_of_ne N.toGW hx (Ne.symm ha)
  rw [he,map_zero]

theorem extendedFunctional_of_mem (N : LogVModule W M) {β : ℂ} (g : Dual ℂ (N.weight β))
    {x : M} (hx : x∈N.weight β) : extendedFunctional N β g x=g ⟨x,hx⟩ := by
  change g (internalProjTo N.isInternal β x)=g ⟨x,hx⟩
  rw [internalProjTo_coe N.isInternal β ⟨x,hx⟩]

/-- A supported actual functional is exactly the extension of its homogeneous restriction. -/
theorem extendedFunctional_restrict (N : LogVModule W M) {β : ℂ} {f : Dual ℂ M}
    (hf : SupportedAt N f β) : extendedFunctional N β (f.domRestrict (N.weight β))=f := by
  apply LinearMap.ext
  intro x
  refine LogFin.induction_on N
    (C := fun x => extendedFunctional N β (f.domRestrict (N.weight β)) x=f x) x ?_ ?_ ?_
  · intro a x hx
    by_cases ha : a=β
    · subst a
      rw [extendedFunctional_of_mem N _ hx]
      rfl
    · have hh := extendedFunctional_supported N β (f.domRestrict (N.weight β)) a ha x hx
      rw [hh,hf a ha x hx]
  · simp
  · intro x y hx hy
    rw [map_add,map_add,hx,hy]

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The literal expansion coefficient is bilinear in the homogeneous outside
functional and homogeneous third vector, with values in the actual inside dual. -/
noncomputable def outsideBlock (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (c β γ : ℂ) (k : ℕ) :
    Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂) :=
  ((outsideCoefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k).compl₂
    (N₃.weight c).subtype) ∘ₗ extendedFunctional N₄ β

/-- This block is exactly the actual unique full-product coefficient map. -/
theorem outsideBlock_apply (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (c β γ : ℂ) (k : ℕ) (g : Dual ℂ (N₄.weight β)) (z : N₃.weight c) :
    outsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k g z=
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (extendedFunctional N₄ β g) z c β γ k := rfl

end VOA.Huang.LogAssocCoefficients
