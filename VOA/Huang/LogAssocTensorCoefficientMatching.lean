import VOA.Huang.LogAssocTensorOuterModes
import VOA.Huang.LogAssocCoefficientTensorPair
import VOA.Huang.LogAssocIterateCoefficients

/-! Literal outer zeroth modes on the canonical genuine tensor have exactly
the original full-product collision coefficients at every log degree.
This is an actual coefficient identity, with no associativity premise. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorCoefficientMatching
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientL0 VOA.Huang.LogAssocTensorOuterModes
open VOA.C2Rigid.LocalInjective VOA.VHat VOA.VHat.DLM3
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Every genuine canonical inner log mode is represented by exactly the
corresponding literal collision coefficient of the original product. -/
theorem tensorOuterModes_innerPair (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (hf : SupportedAt N₄ f β) (γ : ℂ) (k : ℕ) :
    f (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (γ+c-β-1) ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 (a+b-γ-1) k x y) z)=
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y := by
  have hξ : (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 (a+b-γ-1) k x y∈
      (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).weight γ := by
    have hh := (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).2.mem_weight hx hy (a+b-γ-1) k
    convert hh using 1 <;> ring
  rw [tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ (γ+c-β-1) hξ hz f hf,if_pos (by ring)]
  exact tensorIntertwiner_pair_coefficient hC2 N₁ N₂ hfg₁ hfg₂
    N₃ N₄ N₅ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy hf hz

/-- The actual nilpotent lift retains exactly the same zeroth outer pairing. -/
theorem tensorOuterLogModes_innerPair (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (hf : SupportedAt N₄ f β) (γ : ℂ) (k : ℕ) :
    f (tensorOuterLogModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (γ+c-β-1) 0 ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 (a+b-γ-1) k x y) z)=
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y := by
  rw [tensorOuterLogModes_zero]
  exact tensorOuterModes_innerPair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ hx hy hz f hf γ k

end VOA.Huang.LogAssocTensorCoefficientMatching
