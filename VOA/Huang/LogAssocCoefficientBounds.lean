import VOA.Huang.LogAssocSpectrumBounds
import VOA.Huang.LogAssocCoefficientCompatibility

/-! Actual expansion coefficient maps have a common finite collision log
bound and are lower bounded in intermediate generalized weight. These are
bounds on the literal coefficient maps, rather than additional witnesses. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.C2Rigid VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff
open VOA.Huang.LogAssocCoefficientCompatibility
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Vanishing actual input or functional makes the literal full spectrum
product vanish, before any coefficient extraction. -/
theorem spectrumFun_zero_of_input (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅)
    (hfg₅ : FinGen N₅.toWeakModule) (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ)
    (h : x=0 ∨ y=0 ∨ z=0 ∨ f=0) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁ Y₂ f x y z a b c β=(fun _ => 0) := by
  rcases h with rfl | rfl | rfl | rfl <;> funext t <;>
    simp [logProductSpectrumFun,logProductFullCosetFun,logProductIntegerCosetFun,
      prodFunZ,VOA.Huang.AssocCommutator.prodValueZ,
      VOA.Huang.AssocCommutator.prodTermZ,prodCoeff]

/-- Every actual coefficient functional vanishes outside a common finite
collision log range and a genuine per-outside-data weight lower bound. -/
theorem exists_coefficient_bounds (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule) :
    ∃ K : ℕ,∃ M : ℝ,∀ (c β : ℂ) (z : M₃) (f : M₄ →ₗ[ℂ] ℂ),
      z∈N₃.weight c → SupportedAt N₄ f β → ∀ (γ : ℂ) (k : ℕ),
      (K<k ∨ γ.re<M-c.re-β.re) →
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k=0 := by
  obtain ⟨K,M,hB⟩ := exists_spectrum_collision_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  refine ⟨K,M,?_⟩
  intro c β z f hz hf γ k hk
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f z c β γ k hx hy]
  simp only [LinearMap.zero_apply]
  have hzero (h : x=0 ∨ y=0 ∨ z=0 ∨ f=0) :
      logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β)
        (γ-a-b) k=0 := by
    rw [spectrumFun_zero_of_input hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β h]
    exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _
  by_cases ha : N₁.weight a=⊥
  · exact hzero (Or.inl (by simpa only [ha,Submodule.mem_bot] using hx))
  by_cases hb : N₂.weight b=⊥
  · exact hzero (Or.inr (Or.inl (by simpa only [hb,Submodule.mem_bot] using hy)))
  by_cases hc : N₃.weight c=⊥
  · exact hzero (Or.inr (Or.inr (Or.inl (by simpa only [hc,Submodule.mem_bot] using hz))))
  by_cases hβ : N₄.weight β=⊥
  · exact hzero (Or.inr (Or.inr (Or.inr (eq_zero_of_supportedAt_bot hf hβ))))
  obtain ⟨hlog,hweight⟩ := hB a b c β f x y z ha hb hc hβ hx hy hz
  rcases hk with hk | hk
  · exact hlog.2 _ k hk
  · exact hweight.2 _ k (by simp only [Complex.sub_re]; linarith)

/-- The actual restricted-dual generators satisfy the same genuine bounds. -/
theorem exists_restrictedDual_coefficient_bounds (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule) :
    ∃ K : ℕ,∃ M : ℝ,∀ (c β : ℂ) (z : M₃) (r : C2Rigid.RestrictedDual N₄.toGW),
      z∈N₃.weight c → r∈(contraLog N₄).weight β → ∀ (γ : ℂ) (k : ℕ),
      (K<k ∨ γ.re<M-c.re-β.re) →
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (C2Rigid.dualPairingFlip N₄.toGW r) z c β γ k=0 := by
  obtain ⟨K,M,h⟩ := exists_coefficient_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  exact ⟨K,M,fun c β z r hz hr γ k hk =>
    h c β z _ hz (restrictedDual_supportedAt N₄ r hr) γ k hk⟩

end VOA.Huang.LogAssocCoefficients
