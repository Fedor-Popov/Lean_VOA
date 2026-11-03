import VOA.Huang.LogAssocProductIterateIdentity
import VOA.Huang.LogAssocCompletedScaling

/-! The genuine all-logarithmic product-iterate identity at the fixed
positive insertion points z1=3, z2=2, z0=1. Actual conformal transports
carry the overlap identity to these literal chosen branches. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorCoefficientMatching
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.LogAssocTensorOuterModes VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
open VOA.C2Rigid.LocalInjective VOA.VHat VOA.VHat.DLM3
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

/-- Genuine conformal transport scales the actual product-iterate identity
by every chosen conformal parameter, retaining all original logarithms. -/
theorem completedLogProduct_eq_canonical_iterate_shift
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)+s) s a β f ⟨x,hx⟩ y z=
      completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) (t+s) s c β f x y ⟨z,hz⟩ := by
  have hP := completedLogProduct_shift_transport N₁ N₂ N₃ N₄ N₅ Y₁ Y₂
    (Complex.log (1+Complex.exp t)) 0 s a β f ⟨x,hx⟩ y z
  have hI := completedLogIterate_shift_transport N₁ N₂ N₃ N₄
    (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t 0 s c β f x y ⟨z,hz⟩
  simp only [zero_add] at hP hI
  exact hP.trans ((completedLogProduct_eq_canonical_iterate hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (L0exp_mem_weight N₁ (-s) hx) (L0exp_mem_weight N₂ (-s) hy) (L0exp_mem_weight N₃ (-s) hz)
    (f ∘ₗ (L0exp N₄ s).toLinearMap) ht).trans hI.symm)

/-- The fixed points 3,2,1 lie in both genuine convergence regions and give
literal equality of the completed actual logarithmic product and iterate. -/
theorem completedLogProduct_eq_canonical_iterate_three_two_one
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log 3) (Complex.log 2) a β f ⟨x,hx⟩ y z=
      completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) 0 (Complex.log 2) c β f x y ⟨z,hz⟩ := by
  let t : ℂ := (Real.log (1/2) : ℝ)
  let s : ℂ := (Real.log 2 : ℝ)
  have ht : t∈overlapDomain := log_mem_overlapDomain (u := 1/2) (by norm_num) (by norm_num)
  have hExp : Complex.exp t=(1/2 : ℂ) := by
    dsimp only [t]
    rw [← Complex.ofReal_exp,Real.exp_log (by norm_num : (0 : ℝ)<1/2)]
    push_cast
    rfl
  have h2 : s=Complex.log 2 := by
    dsimp only [s]
    exact Complex.ofReal_log (by norm_num : (0 : ℝ)≤2)
  have h0 : t+s=0 := by
    dsimp only [t,s]
    rw [← Complex.ofReal_add,← Real.log_mul (by norm_num : (1/2 : ℝ)≠0) (by norm_num : (2 : ℝ)≠0)]
    norm_num
  have h3 : Complex.log (1+Complex.exp t)+s=Complex.log 3 := by
    rw [hExp]
    have he : (1 : ℂ)+1/2=((3/2 : ℝ) : ℂ) := by push_cast; ring
    rw [he,← Complex.ofReal_log (by norm_num : (0 : ℝ)≤3/2)]
    dsimp only [s]
    rw [← Complex.ofReal_add,← Real.log_mul (by norm_num : (3/2 : ℝ)≠0) (by norm_num : (2 : ℝ)≠0)]
    norm_num [Complex.ofReal_log (by norm_num : (0 : ℝ)≤3)]
  have he := completedLogProduct_eq_canonical_iterate_shift (β := β) hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f ht s
  rw [h3,h0,h2] at he
  exact he

end VOA.Huang.LogAssocTensorCoefficientMatching
