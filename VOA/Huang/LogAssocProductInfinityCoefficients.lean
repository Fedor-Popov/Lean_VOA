import VOA.Huang.LogAssocProductInfinityExpansion

/-! Original product mode coefficients are exactly the Frobenius coefficients
at infinity. The literal chosen logarithm -sigma retains the sign (-1)^k,
and the real lower intermediate spectrum selects each weight exactly once. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.LogHuangODEProduct
open VOA.Huang.LogHuangODEIterPoint VOA.Huang.LogRemovalCoeff
open VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion VOA.Huang.AssocCoeffRules
open Classical
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
/-- The full genuine infinity product sums every actual lower spectrum row once. -/
noncomputable def productInfinitySpectrum (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅)
    (hfg₅ : FinGen N₅.toWeakModule) (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β σ : ℂ) : ℂ :=
  ∑ mu∈spectrumCosets hC2 N₅ hfg₅,
    productInfinityRow Y₁ Y₂ f x y z a b c β (lowerSpectrumRep hC2 N₅ hfg₅ mu) σ

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
  (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- Every actual product infinity row has the exact original mode coefficient. -/
theorem logCoeff_productInfinityRow (r γ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (productInfinityRow Y₁.1 Y₂.1 f x y z a b c β r) (a+γ-β) k=
      if ∃ n : ℕ,r+n=γ then
        (-1:ℂ)^k*f (Y₁.1 (a+γ-β-1) k x (Y₂.1 (b+c-γ-1) 0 y z)) else 0 := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  let H (l : ℕ) := productInfinitySeries Y₁.1 Y₂.1 f x y z a b c β r l
  let F (l : ℕ) (σ : ℂ) := (-1:ℂ)^l*(σ^l*Complex.exp ((a+r-β)*σ)*psEval (H l) (Complex.exp σ))
  have hH (l : ℕ) : H l∈SubexpPS := productInfinitySeries_mem hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β r l
  have hF (l : ℕ) : HasLogExp overlapDomain (F l) :=
    hasLogExp_smul ((-1:ℂ)^l) (hasLogExp_monomial_psEval (hH l) (a+r-β) l)
  have hR : HasLogExp overlapDomain (productInfinityRow Y₁.1 Y₂.1 f x y z a b c β r) := by
    obtain ⟨E,hE⟩ := productInfinityRow_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β r
    exact ⟨E,fun σ hσ => hE σ (overlapDomain_subset hσ)⟩
  have hrow (σ : ℂ) : productInfinityRow Y₁.1 Y₂.1 f x y z a b c β r σ=
      ∑ l∈Finset.range K,F l σ := by
    rw [productInfinityRow_eq_sum_log Y₂.1 (fun n l hl => hK Y₁ n l hl)]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp only [F,H]
    rw [show -σ=(-1:ℂ)*σ by ring,mul_pow]
    ring
  rw [logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun σ _ => hrow σ) hR,
    logCoeff_sum isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (Finset.range K) (fun l _ => hF l)]
  dsimp only [F]
  simp_rw [logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    _ (hasLogExp_monomial_psEval (hH _) (a+r-β) _),logCoeff_monomial_psEval (hH _)]
  by_cases hγ : ∃ n : ℕ,r+n=γ
  · obtain ⟨n,hn⟩ := hγ
    rw [if_pos ⟨n,hn⟩]
    have hμ : a+γ-β=(a+r-β)+(n:ℂ) := by linear_combination -hn
    conv_lhs => rw [hμ]
    simp_rw [exCoeff_of_eq,Polynomial.coeff_monomial]
    have hc (l : ℕ) : PowerSeries.coeff n (H l)=
        f (Y₁.1 (a+γ-β-1) l x (Y₂.1 (b+c-γ-1) 0 y z)) := by
      simp only [H,productInfinitySeries,PowerSeries.coeff_mk]
      rw [show a+r-β-1+(n:ℂ)=a+γ-β-1 by linear_combination hn,
        show b+c-r-1-(n:ℂ)=b+c-γ-1 by linear_combination -hn]
    by_cases hk : k<K
    · rw [Finset.sum_eq_single k]
      · rw [if_pos rfl,hc k]
      · intro l hl hlk
        rw [if_neg hlk,mul_zero]
      · intro hk'
        exact False.elim (hk' (Finset.mem_range.mpr hk))
    · have hz : Y₁.1 (a+γ-β-1) k=0 := hK Y₁ _ k (by omega)
      rw [hz,LinearMap.zero_apply,LinearMap.zero_apply,map_zero,mul_zero]
      apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg (by have := Finset.mem_range.mp hl; omega),mul_zero]
  · rw [if_neg hγ]
    apply Finset.sum_eq_zero
    intro l hl
    rw [exCoeff_of_forall_ne (by intro n he; exact hγ ⟨n,by linear_combination he⟩),mul_zero]

/-- Every full actual infinity product has a true Frobenius expansion on the half-plane. -/
theorem productInfinitySpectrum_hasLogExp :
    HasLogExp halfPlane (productInfinitySpectrum hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β) :=
  hasLogExp_sum _ fun mu _ => productInfinityRow_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β _

/-- The complete actual spectrum coefficient is exactly its original product mode value. -/
theorem logCoeff_productInfinitySpectrum {b c : ℂ} {y : M₂} {z : M₃}
    (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) (γ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (productInfinitySpectrum hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β) (a+γ-β) k=
      (-1:ℂ)^k*f (Y₁.1 (a+γ-β-1) k x (Y₂.1 (b+c-γ-1) 0 y z)) := by
  classical
  unfold productInfinitySpectrum
  rw [logCoeff_sum isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (spectrumCosets hC2 N₅ hfg₅) (fun mu _ => by
      obtain ⟨E,hE⟩ := productInfinityRow_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β (lowerSpectrumRep hC2 N₅ hfg₅ mu)
      exact ⟨E,fun σ hσ => hE σ (overlapDomain_subset hσ)⟩)]
  simp_rw [logCoeff_productInfinityRow hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β]
  apply lowerSpectrum_indicator hC2 N₅ hfg₅
  intro hC hbot
  have hm := Y₂.2.mem_weight hy hz (b+c-γ-1) 0
  rw [show b+c-(b+c-γ-1)-1=γ by ring,hbot] at hm
  have hY : Y₂.1 (b+c-γ-1) 0 y z=0 := (Submodule.mem_bot ℂ).mp hm
  apply hC
  rw [hY,map_zero,map_zero,mul_zero]

end VOA.Huang.LogAssocExpansion
