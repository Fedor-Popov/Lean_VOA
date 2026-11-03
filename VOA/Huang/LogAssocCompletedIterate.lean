import VOA.Huang.LogAssocIterateExpansion

/-! Literal completed evaluations of genuine logarithmic iterates agree with
actual convergent lower spectrum rows. The full branch and every genuine
log coefficient are retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.FrobeniusLog
open VOA.Huang.LogHuangODEIterate VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.AssocCoeffRules (hasLogExp_sum hasLogExp_congr)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Pair an actual completed first input with the genuine outer evaluation block. -/
noncomputable def completedIteratePair
    (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (ell c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (q : Completion N₅) (z : N₃.weight c) : ℂ :=
  ∑' γ : ℂ,f (pointEvaluationBlock N₅ N₃ N₄ Y₃ ell γ c β (q γ) z)

/-- Literal composition of the genuine completed point evaluations in iterate order. -/
noncomputable def completedLogIterate
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ell₀ ell₂ c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : N₃.weight c) : ℂ :=
  completedIteratePair N₃ N₄ N₅ Y₃ ell₂ c β f (evaluatePoint N₁ N₂ N₅ Y₄ ell₀ x y) z

/-- The literal finite disjoint intermediate spectrum expression for a full true iterate. -/
noncomputable def logIterateSpectrumFun (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅)
    (hfg₅ : FinGen N₅.toWeakModule) (Y₃ : LogModes M₅ M₃ M₄) (Y₄ : LogModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β t : ℂ) : ℂ :=
  ∑ mu∈spectrumCosets hC2 N₅ hfg₅,
    logIterateLowerCosetFun Y₃ Y₄ f x y z α₁ α₂ α₃ β (lowerSpectrumRep hC2 N₅ hfg₅ mu) t

private theorem pointEvaluationBlock_zero
    (A₁ : LogVModule W M₅) (A₂ : LogVModule W M₃) (A₃ : LogVModule W M₄)
    (Y : LogIntertwiningOperator A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule)
    (a b c : ℂ) (x : A₁.weight a) (y : A₂.weight b) :
    (pointEvaluationBlock A₁ A₂ A₃ Y 0 a b c x y : M₄)=Y.1 (a+b-c-1) 0 x y := by
  unfold pointEvaluationBlock
  simp only [zero_mul,Complex.exp_zero,one_smul]
  rw [Finset.sum_eq_single 0]
  · simp [logarithmicBlock]
  · intro k hk hk0
    rw [zero_pow hk0,zero_smul]
  · intro hh
    exfalso
    apply hh
    simp only [Finset.mem_range,pointLogCutoff]
    omega

/-- The literal all-log completed iterate equals its actual lower spectrum
series on the overlap, with convergence of the entire weight sum proved. -/
theorem completedLogIterate_eq_lowerSpectrum (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight α₁) (hy : y∈N₂.weight α₂) (hz : z∈N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ t 0 α₃ β f x y ⟨z,hz⟩=
      logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β t := by
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
    rw [pointEvaluationBlock_zero N₅ N₃ N₄ Y₃ γ α₃ β (q γ) ⟨z,hz⟩]
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
  have hsum := (tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows).2
  change (∑' γ : ℂ,g γ)=_
  rw [hsum]
  unfold logIterateSpectrumFun
  refine Finset.sum_congr rfl fun mu hmu => ?_
  rw [tsum_congr (hrow (lowerSpectrumRep hC2 N₅ hfg₅ mu)),
    Summable.tsum_finsetSum (fun l _ => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) l).mul_left
      (t^l*Complex.exp ((lowerSpectrumRep hC2 N₅ hfg₅ mu-α₁-α₂)*t))),
    lowerIterate_eq_sum_log Y₃.1 hzero]
  simp only [tsum_mul_left,psEval]

/-- The entire actual true logarithmic iterate spectrum has a finite
convergent Frobenius expansion, for arbitrary input vectors. -/
theorem log_iterate_spectrum_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β : ℂ) :
    VOA.Huang.LogRemovalCoeff.HasLogExp overlapDomain
      (logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β) :=
  hasLogExp_sum _ fun mu _ => log_iterate_lowerCoset_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z α₁ α₂ α₃ β _

/-- Literal completed composition of the genuine logarithmic evaluations
has an honest finite convergent collision expansion. -/
theorem completedLogIterate_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight α₁) (hy : y∈N₂.weight α₂) (hz : z∈N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) :
    VOA.Huang.LogRemovalCoeff.HasLogExp overlapDomain
      (fun t => completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ t 0 α₃ β f x y ⟨z,hz⟩) :=
  hasLogExp_congr (fun t ht => (completedLogIterate_eq_lowerSpectrum hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ hx hy hz f β ht).symm)
    (log_iterate_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₃ Y₄ f x y z α₁ α₂ α₃ β)

end VOA.Huang.LogAssocExpansion
