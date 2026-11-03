import VOA.Classification.COne.McRaeM2TensorNestedGeneration

/-! Genuine homogeneous nested canonical coefficients determine every
linear map from the actual left-associated triple tensor carrier. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- Actual homogeneous zero-log nested coefficients determine arbitrary
linear maps, including those which have no module-homomorphism structure. -/
theorem leftTriple_linearMap_ext_homogeneous
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f g : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] X}
    (h : ∀ (n m a b c : ℂ) (x : M₁) (y : M₂) (z : M₃),
      x∈N₁.weight a → y∈N₂.weight b → z∈N₃.weight c →
      f ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n 0
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m 0 x y) z)=
      g ((tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃).1 n 0
        ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 m 0 x y) z)) : f=g := by
  let T := tensorModule hC2 N₁ N₂ h₁ h₂
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₁ N₂ h₁ h₂
  let η := tensorIntertwiner hC2 T N₃ hfgT h₃
  apply tensor_linearMap_ext_homogeneous hC2 T N₃ hfgT h₃
  intro n γ c w z hw hz
  let A := (η.1 n 0).flip z
  have hfg : f ∘ₗ A=g ∘ₗ A := by
    apply tensor_linearMap_ext_homogeneous hC2 N₁ N₂ h₁ h₂
    intro m a b x y hx hy
    exact h n m a b c x y z hx hy hz
  exact LinearMap.congr_fun hfg w

end VOA.C2Rigid.LocalInjective
