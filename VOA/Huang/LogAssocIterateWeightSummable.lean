import VOA.Huang.LogAssocCreationEvaluation

/-! Actual C2 logarithmic iterate convergence includes the entire literal
complex intermediate-weight sum. This supports true scalar linearity on
actual homogeneous input spaces without discarding Jordan/logarithmic terms. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.FrobeniusLog
open VOA.Huang.LogHuangODEIterate VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Every actual intermediate generalized weight in a genuine logarithmic
iterate is included in an absolutely summable scalar array. -/
theorem completedLogIterate_weight_summable (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight α₁) (hy : y∈N₂.weight α₂) (hz : z∈N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    Summable (fun γ : ℂ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ 0 γ α₃ β
      (evaluatePoint N₁ N₂ N₅ Y₄ t x y γ) ⟨z,hz⟩)) := by
  classical
  let q := evaluatePoint N₁ N₂ N₅ Y₄ t x y
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ 0 γ α₃ β (q γ) ⟨z,hz⟩)
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  have hzero : ∀ n l,K≤l → Y₄.1 n l=0 := fun n l hl => hK Y₄ n l hl
  have hq (γ : ℂ) : (q γ : M₅)=Complex.exp (t*(γ-α₁-α₂)) •
      ∑ l∈Finset.range K,t^l•Y₄.1 (α₁+α₂-γ-1) l x y := by
    dsimp only [q]
    rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
    exact pointEvaluationBlock_fixed_cutoff N₁ N₂ N₅ Y₄ t α₁ α₂ γ ⟨x,hx⟩ ⟨y,hy⟩ K
      (fun l hl => by rw [hzero _ l hl]; rfl)
  have hg (γ : ℂ) : g γ=Complex.exp (t*(γ-α₁-α₂)) *
      ∑ l∈Finset.range K,t^l*f (Y₃.1 (γ+α₃-β-1) 0 (Y₄.1 (α₁+α₂-γ-1) l x y) z) := by
    dsimp only [g]
    rw [pointEvaluationBlock_branch_zero N₅ N₃ N₄ Y₃ γ α₃ β (q γ) ⟨z,hz⟩]
    rw [hq,map_smul,LinearMap.smul_apply,map_smul,map_sum,LinearMap.sum_apply,map_sum]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  have hweight : ∀ γ,g γ≠0 → N₅.weight γ≠⊥ := by
    intro γ hγ he
    have hq0 : q γ=0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ≤(⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g,hq0,map_zero,LinearMap.zero_apply,Submodule.coe_zero]
  have hrow (r : ℂ) (n : ℕ) : g (r+n)=
      ∑ l∈Finset.range K,t^l*Complex.exp ((r-α₁-α₂)*t)*
        (PowerSeries.coeff n (logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r l)*
          (Complex.exp t)^n) := by
    rw [hg,Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [logIterateLowerCosetSeries,PowerSeries.coeff_mk]
    have he : Complex.exp (t*(r+(n : ℂ)-α₁-α₂))=
        Complex.exp ((r-α₁-α₂)*t)*(Complex.exp t)^n := by
      rw [show t*(r+(n : ℂ)-α₁-α₂)=(r-α₁-α₂)*t+(n : ℂ)*t by ring,
        Complex.exp_add,Complex.exp_nat_mul]
    rw [he]
    have hn : α₁+α₂-(r+(n : ℂ))-1=α₁+α₂-r-1-n := by ring
    have ho : r+(n : ℂ)+α₃-β-1=r+α₃-β-1+n := by ring
    rw [hn,ho]
    ring
  have hs (r : ℂ) (l : ℕ) : Summable fun n : ℕ =>
      PowerSeries.coeff n (logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r l)*(Complex.exp t)^n := by
    simpa only [logIterateLowerCosetSeries,PowerSeries.coeff_mk] using
      summable_log_iterate_series hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
        f x y z (r+α₃-β-1) (α₁+α₂-r-1) 0 l (by rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr ht.1)
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N₅ hfg₅ mu+n) := by
    intro mu hmu
    have hh := summable_sum fun l (hl : l∈Finset.range K) =>
      (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) l).mul_left
        (t^l*Complex.exp ((lowerSpectrumRep hC2 N₅ hfg₅ mu-α₁-α₂)*t))
    exact hh.congr fun n => (hrow _ n).symm
  exact (tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows).1

end VOA.Huang.LogAssocExpansion
