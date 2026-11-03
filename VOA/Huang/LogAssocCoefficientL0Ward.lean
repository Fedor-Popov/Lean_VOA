import VOA.Huang.LogAssocCoefficientL0SpectrumDerivative
import VOA.Huang.LogAssocCoefficientL0Action

/-! The actual generalized L(0) Ward equation for genuine all-logarithmic
collision coefficients. Both source Jordan operators and the collision
logarithm successor remain present. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz
open Module (End)
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.LogAssocCoefficients
open scoped BigOperators
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
  (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- Actual L(-1) source insertion yields the genuine collision coefficient derivative. -/
theorem coefficient_Lm1_left (k : ℕ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
      (Lm1 N₁.toWeakModule x) y =
      (γ-a-b)*coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y +
      ((k:ℂ)+1)*coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ (k+1) x y := by
  have hxL : Lm1 N₁.toWeakModule x∈N₁.weight (a+1) := by
    have hh := N₁.mode_mem_weight W.conformalVector_mem_grading_two hx 0
    convert hh using 1
    congr 1
    norm_num
    ring
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hxL hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ (k+1) hx hy]
  let F := logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β
  have hF : HasLogExp overlapDomain F := log_product_spectrum_hasLogExp hC2
    N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  obtain ⟨hD,hDc⟩ := logCoeff_deriv isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF (γ-a-b) k
  have hE := hasLogExp_exp_mul hD (-1)
  have he (t : ℂ) (ht : t∈overlapDomain) := spectrum_Lm1_eq hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β ht
  rw [logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => he t ht) (hasLogExp_congr (fun t ht => (he t ht).symm) hE),
    show γ-(a+1)-b=(γ-a-b)+ -1 by ring,
    logCoeff_exp_mul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hD,hDc]

/-- The literal coefficient functionals satisfy the full actual generalized-L(0) equation. -/
theorem coefficient_L0_Ward (k : ℕ) :
    (dualL0 N₁ N₂-γ • (1 : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂))))
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) =
      ((k:ℂ)+1) • coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ (k+1) +
      preFirst N₁.L0nil (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) +
      preSecond N₂.L0nil (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    dualL0_apply,LinearMap.add_apply,preFirst_apply,preSecond_apply]
  rw [coefficient_Lm1_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy,
    N₁.L0nil_apply_of_mem hx,N₂.L0nil_apply_of_mem hy]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul]
  ring

end VOA.Huang.LogAssocCoefficientL0
