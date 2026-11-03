import VOA.Huang.LogAssocIterateCoefficients

/-! Actual convergent logarithmic iterate coefficients are detected by the
literal completed evaluations. Every genuine logarithmic degree is kept. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Zero true completed iterates force all original inner logarithmic
coefficients, paired with the genuine outer zeroth coefficient, to vanish. -/
theorem iterate_mode_zero_of_completed_zero (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ)
    (hzero : ∀ t∈overlapDomain,
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ t 0 c β f x y ⟨z,hz⟩=0)
    (γ : ℂ) (k : ℕ) : f (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) k x y) z)=0 := by
  let F := logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 f x y z a b c β
  have hF : HasLogExp overlapDomain F := log_iterate_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z a b c β
  have hF0 : ∀ t∈overlapDomain,F t=0 := by
    intro t ht
    exact (completedLogIterate_eq_lowerSpectrum hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ hx hy hz f β ht).symm.trans (hzero t ht)
  have hc : logCoeff overlapDomain F (γ-a-b) k=0 := by
    rw [logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF0 hF]
    exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _
  exact (logCoeff_iterateSpectrum hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₃ Y₄ hx hy f z c β γ k).symm.trans hc

/-- Equal true completed iterate pairings give equal original genuine
logarithmic mode pairings, without a functional linearity assumption. -/
theorem iterate_mode_eq_of_completed_eq (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f g : M₄ →ₗ[ℂ] ℂ) (β : ℂ)
    (heq : ∀ t∈overlapDomain,
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ t 0 c β f x y ⟨z,hz⟩=
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ t 0 c β g x y ⟨z,hz⟩)
    (γ : ℂ) (k : ℕ) :
    f (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) k x y) z)=
      g (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) k x y) z) := by
  let F := logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 f x y z a b c β
  let G := logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 g x y z a b c β
  have hF : HasLogExp overlapDomain F := log_iterate_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z a b c β
  have hFG : ∀ t∈overlapDomain,F t=G t := by
    intro t ht
    exact (completedLogIterate_eq_lowerSpectrum hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ hx hy hz f β ht).symm.trans
      ((heq t ht).trans (completedLogIterate_eq_lowerSpectrum hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ hx hy hz g β ht))
  exact (logCoeff_iterateSpectrum hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₃ Y₄ hx hy f z c β γ k).symm.trans
    ((logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hFG hF
      (γ-a-b) k).trans
      (logCoeff_iterateSpectrum hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₃ Y₄ hx hy g z c β γ k))

end VOA.Huang.LogAssocExpansion
