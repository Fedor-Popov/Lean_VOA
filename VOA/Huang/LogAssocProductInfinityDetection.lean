import VOA.Huang.LogAssocProductInfinityCompleted
import VOA.Huang.LogAssocProductInfinityChart

/-! Vanishing of the actual completed logarithmic product on the overlap
forces every original product mode matrix coefficient to vanish. The
literal infinity Frobenius coefficients and the proved strict chart supply
the detection; no associativity or semisimplicity witness is assumed. -/
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

/-- Actual completed-product vanishing detects every original logarithmic
mode coefficient, retaining all generalized module Jordan degrees. -/
theorem product_mode_zero_of_completed_zero (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ)
    (hzero : ∀ t∈overlapDomain,
      completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0
        a β f ⟨x,hx⟩ y z=0) (γ : ℂ) (k : ℕ) :
    f (Y₁.1 (a+γ-β-1) k x (Y₂.1 (b+c-γ-1) 0 y z))=0 := by
  let F := productInfinitySpectrum hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β
  have hF : HasLogExp halfPlane F := productInfinitySpectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hchart : ∀ t∈overlapDomain,F (productInfinityChart t)=0 := by
    intro t ht
    have he := completedLogProduct_eq_infinitySpectrum hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f β (productInfinityChart_mem_halfPlane ht)
    dsimp only [F]
    rw [← he]
    simpa only [productInfinityChart,neg_neg] using hzero t ht
  have hzF := infinity_zero_of_chart_zero hF hchart
  have hF' : HasLogExp overlapDomain F := by
    obtain ⟨E,hE⟩ := hF
    exact ⟨E,fun σ hσ => hE σ (overlapDomain_subset hσ)⟩
  have hc : logCoeff overlapDomain F (a+γ-β) k=0 := by
    rw [logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (fun σ hσ => hzF σ (overlapDomain_subset hσ)) hF']
    exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _
  dsimp only [F] at hc
  rw [logCoeff_productInfinitySpectrum hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f x a β hy hz γ k] at hc
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero k (by norm_num : (-1:ℂ)≠0))

end VOA.Huang.LogAssocExpansion
