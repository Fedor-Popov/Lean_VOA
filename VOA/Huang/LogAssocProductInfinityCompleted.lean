import VOA.Huang.LogAssocProductInfinityCoefficients

/-! The actual completed logarithmic product at the chosen infinity branch
is the literal finite lower-spectrum Frobenius expression. Absolute
convergence of every actual intermediate weight is proved. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.FrobeniusLog
open VOA.Huang.LogHuangODEProduct VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.AssocCoeffRules (hasLogExp_sum hasLogExp_congr)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The actual chosen-branch completed product at infinity equals every
convergent genuine lower spectral row, retaining all outer logarithms. -/
theorem completedLogProduct_eq_infinitySpectrum (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {σ : ℂ} (hσ : σ∈halfPlane) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (-σ) 0 a β f ⟨x,hx⟩ y z=
      productInfinitySpectrum hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β σ := by
  classical
  let q := evaluatePoint N₂ N₃ N₅ Y₂ 0 y z
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₁ N₅ N₄ Y₁ (-σ) a γ β ⟨x,hx⟩ (q γ))
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  have hq (γ : ℂ) : (q γ : M₅)=Y₂.1 (b+c-γ-1) 0 y z := by
    dsimp only [q]
    rw [evaluatePoint_zero,evaluateOne_homogeneous N₂ N₃ N₅ Y₂ hy hz γ]
  have hg (γ : ℂ) : g γ=Complex.exp ((a+γ-β)*σ) *
      ∑ k∈Finset.range K,(-σ)^k*f (Y₁.1 (a+γ-β-1) k x (Y₂.1 (b+c-γ-1) 0 y z)) := by
    dsimp only [g]
    rw [pointEvaluationBlock_fixed_cutoff N₁ N₅ N₄ Y₁ (-σ) a γ β ⟨x,hx⟩ (q γ) K
      (fun k hk => by rw [hzero _ k hk]; rfl),map_smul,map_sum]
    simp only [map_smul,smul_eq_mul,hq]
    rw [show (-σ)*(β-a-γ)=(a+γ-β)*σ by ring]
  have hweight : ∀ γ,g γ≠0 → N₅.weight γ≠⊥ := by
    intro γ hγ he
    have hq0 : q γ=0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ≤(⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g,hq0,map_zero,Submodule.coe_zero]
  have hrow (r : ℂ) (n : ℕ) : g (r+n)=
      ∑ k∈Finset.range K,(-σ)^k*Complex.exp ((a+r-β)*σ)*
        (PowerSeries.coeff n (productInfinitySeries Y₁.1 Y₂.1 f x y z a b c β r k)*(Complex.exp σ)^n) := by
    rw [hg,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [productInfinitySeries,PowerSeries.coeff_mk]
    have he : Complex.exp ((a+(r+(n:ℂ))-β)*σ)=
        Complex.exp ((a+r-β)*σ)*(Complex.exp σ)^n := by
      rw [show (a+(r+(n:ℂ))-β)*σ=(a+r-β)*σ+(n:ℂ)*σ by ring,
        Complex.exp_add,Complex.exp_nat_mul]
    rw [he,show a+(r+(n:ℂ))-β-1=a+r-β-1+n by ring,
      show b+c-(r+(n:ℂ))-1=b+c-r-1-n by ring]
    ring
  have hs (r : ℂ) (k : ℕ) : Summable fun n : ℕ =>
      PowerSeries.coeff n (productInfinitySeries Y₁.1 Y₂.1 f x y z a b c β r k)*(Complex.exp σ)^n := by
    simpa only [productInfinitySeries,PowerSeries.coeff_mk] using
      summable_log_product_series hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f x y z (a+r-β-1) (b+c-r-1) k 0
        (by rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr hσ)
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N₅ hfg₅ mu+n) := by
    intro mu hmu
    have hh := summable_sum fun k (hk : k∈Finset.range K) =>
      (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k).mul_left
        ((-σ)^k*Complex.exp ((a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β)*σ))
    exact hh.congr fun n => (hrow _ n).symm
  have hsum := (tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows).2
  change (∑' γ : ℂ,g γ)=_
  rw [hsum]
  unfold productInfinitySpectrum
  apply Finset.sum_congr rfl
  intro mu hmu
  rw [tsum_congr (hrow (lowerSpectrumRep hC2 N₅ hfg₅ mu)),
    Summable.tsum_finsetSum (fun k _ => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k).mul_left
      ((-σ)^k*Complex.exp ((a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β)*σ))),
    productInfinityRow_eq_sum_log Y₂.1 hzero]
  simp only [tsum_mul_left,psEval]

end VOA.Huang.LogAssocExpansion
