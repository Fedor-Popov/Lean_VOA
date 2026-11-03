import VOA.Huang.LogAssocOuterModes
import VOA.Huang.LogAssocCoefficientCoproductStable

/-! The actual expansion coefficients, with their proved span membership,
construct literal outer zeroth modes by finite-weight duality. Jacobi
and the coupled derivative are separate remaining mathematical identities. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficientCompatibility VOA.Huang.LogAssocCoefficientCoproduct
open Module (Dual)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- The literal outside coefficient block, valued in the proved actual coefficient span. -/
noncomputable def spanOutsideBlock (c β γ : ℂ) (k : ℕ) :
    Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ]
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ := by
  let B := outsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k
  have hB (g : Dual ℂ (N₄.weight β)) (z : N₃.weight c) : B g z∈
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
    coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (extendedFunctional N₄ β g) z c β γ k (extendedFunctional_supported N₄ β g) z.2
  refine LinearMap.mk₂ ℂ (fun g z => ⟨B g z,hB g z⟩) ?_ ?_ ?_ ?_
  · intro g h z
    apply Subtype.ext
    exact congrArg (fun F => F z) (B.map_add g h)
  · intro s g z
    apply Subtype.ext
    exact congrArg (fun F => F z) (B.map_smul s g)
  · intro g z z'
    apply Subtype.ext
    exact (B g).map_add z z'
  · intro s g z
    apply Subtype.ext
    exact (B g).map_smul s z

variable {R : Type u} [AddCommGroup R] [Module ℂ R]
variable (N : LogVModule W R)
variable (χ : coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ →ₗ[ℂ] R)

/-- Map the actual coefficient span to a stated genuine module. -/
noncomputable def mappedOutsideBlock (c β γ : ℂ) (k : ℕ) :
    Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R :=
by
  let B := spanOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k
  refine LinearMap.mk₂ ℂ (fun g z => χ (B g z)) ?_ ?_ ?_ ?_
  · intro g h z
    dsimp only
    rw [map_add,LinearMap.add_apply,map_add]
  · intro s g z
    dsimp only
    rw [map_smul,LinearMap.smul_apply,map_smul]
  · intro g z z'
    dsimp only
    rw [map_add,map_add]
  · intro s g z
    dsimp only
    rw [map_smul,map_smul]

/-- The mapped actual block is literal linear postcomposition. -/
theorem mappedOutsideBlock_apply (c β γ : ℂ) (k : ℕ)
    (g : Dual ℂ (N₄.weight β)) (z : N₃.weight c) :
    mappedOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ χ c β γ k g z=
      χ (spanOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k g z) := rfl

/-- The actual span block has its literal outside coefficient as underlying value. -/
theorem spanOutsideBlock_coe (c β γ : ℂ) (k : ℕ)
    (g : Dual ℂ (N₄.weight β)) (z : N₃.weight c) :
    (spanOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k g z : BilinearDual (M₁ := M₁) (M₂ := M₂))=
      outsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k g z := rfl

/-- Outer zeroth modes reconstructed from the actual full-product coefficients. -/
noncomputable def coefficientOuterModes (n : ℂ) :
    C2Rigid.RestrictedDual N.toGW →ₗ[ℂ] M₃ →ₗ[ℂ] M₄ :=
  outerModes N N₃ N₄ (fun β γ c =>
    mappedOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ χ c β γ 0) n

/-- These literal modes have the genuine generalized target weight. -/
theorem coefficientOuterModes_weight (n : ℂ) :
    HasModeWeight (contraLog N) N₃ N₄ n
      (coefficientOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ N χ n) :=
  outerModes_weight N N₃ N₄ _ n

/-- These actual recovered outer modes are lower truncated on arbitrary inputs. -/
theorem coefficientOuterModes_truncated (ξ : C2Rigid.RestrictedDual N.toGW) (z : M₃) (n : ℂ) :
    ∃ K : ℤ,∀ j : ℤ,K≤j →
      coefficientOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ N χ (n+j) ξ z=0 :=
  outerModes_truncated N N₃ N₄ _ ξ z n

/-- Pairing the literal recovered outer mode gives exactly the original
actual collision coefficient, with all foreign target weights zero. -/
theorem coefficientOuterModes_pair (n : ℂ) {γ c β : ℂ}
    {ξ : C2Rigid.RestrictedDual N.toGW} {z : M₃}
    (hξ : ξ∈(contraLog N).weight γ) (hz : z∈N₃.weight c)
    (f : Dual ℂ M₄) (hf : SupportedAt N₄ f β) :
    f (coefficientOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ N χ n ξ z)=
      if β=γ+c-n-1 then C2Rigid.dualPairing N.toGW
        (χ ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
          coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩) ξ
        else 0 := by
  rw [coefficientOuterModes,outerModes_pair N N₃ N₄ _ n hξ hz f hf]
  split_ifs with h
  · have he : mappedOutsideBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ χ c β γ 0
        (f.domRestrict (N₄.weight β)) ⟨z,hz⟩=
        χ ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
          coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩ := by
      rw [mappedOutsideBlock_apply]
      apply congrArg χ
      apply Subtype.ext
      rw [spanOutsideBlock_coe,outsideBlock_apply,extendedFunctional_restrict N₄ hf]
    exact congrArg (fun r => C2Rigid.dualPairing N.toGW r ξ) he
  · rfl

end VOA.Huang.LogAssocCoefficients
