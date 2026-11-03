import VOA.Huang.LogAssocCompletedIterate
import VOA.Huang.LogAssocSpectrumSelector

/-! Unique logarithmic coefficients of the actual completed iterate are
its literal operator mode coefficients. Actual spectrum support and the
proved disjoint lower rows prevent omissions and duplicate exponents. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.LogHuangODEIterate
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

/-- Actual convergent monomial-log coefficients agree with the literal formal coefficients. -/
theorem logCoeff_monomial_psEval {G : PowerSeries ℂ} (hG : G∈SubexpPS) (lam : ℂ) (l : ℕ)
    (μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (fun t => t^l*Complex.exp (lam*t)*psEval G (Complex.exp t)) μ k=
      exCoeff lam (fun n => Polynomial.monomial l (PowerSeries.coeff n G)) μ k := by
  let p : ℕ → Polynomial ℂ := fun n => Polynomial.monomial l (PowerSeries.coeff n G)
  have hp : LogGood p := by
    refine ⟨⟨l,fun n => Polynomial.natDegree_monomial_le _⟩,?_⟩
    intro j
    by_cases hj : j=l
    · subst j
      simpa only [p,Polynomial.coeff_monomial,ite_true] using (mem_subexpPS.mp hG)
    · have he : (fun n => ‖(p n).coeff j‖)=(fun _ => (0 : ℝ)) := by
        funext n
        simp [p,Polynomial.coeff_monomial,hj,Ne.symm hj]
      rw [he]
      exact subexponential_zero
  apply logCoeff_logFun isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hp
  intro t ht
  unfold logFun psEval
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [p,Polynomial.eval_monomial,Complex.exp_add,add_mul,Complex.exp_nat_mul]
  ring

/-- Every genuine logarithmic degree on a lower intermediate row has exactly
its corresponding literal operator coefficient. -/
theorem logCoeff_lowerIterate (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β r γ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (logIterateLowerCosetFun Y₃.1 Y₄.1 f x y z a b c β r) (γ-a-b) k=
      if ∃ n : ℕ,r+n=γ then f (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) k x y) z) else 0 := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  let H (l : ℕ) := logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z a b c β r l
  let F (l : ℕ) (t : ℂ) := t^l*Complex.exp ((r-a-b)*t)*psEval (H l) (Complex.exp t)
  have hH (l : ℕ) : H l∈SubexpPS := by
    apply subexp_of_summable_unitDisc
    intro t ht
    simpa only [H,logIterateLowerCosetSeries,PowerSeries.coeff_mk] using
      summable_log_iterate hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
        f x y z (r+c-β-1) (a+b-r-1) 0 l ht
  have hF (l : ℕ) : HasLogExp overlapDomain (F l) :=
    hasLogExp_monomial_psEval (hH l) (r-a-b) l
  have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t _ => lowerIterate_eq_sum_log Y₃.1 (fun n l hl => hK Y₄ n l hl) f x y z a b c β r t)
    (log_iterate_lowerCoset_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₃ Y₄ f x y z a b c β r) (γ-a-b) k
  rw [he,logCoeff_sum isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (Finset.range K) (fun l _ => hF l)]
  dsimp only [F]
  simp_rw [logCoeff_monomial_psEval (hH _)]
  by_cases hγ : ∃ n : ℕ,r+n=γ
  · obtain ⟨n,hn⟩ := hγ
    rw [if_pos ⟨n,hn⟩]
    have hμ : γ-a-b=(r-a-b)+(n : ℂ) := by linear_combination -hn
    rw [hμ]
    simp_rw [exCoeff_of_eq,Polynomial.coeff_monomial]
    have hc (l : ℕ) : PowerSeries.coeff n (H l)=
        f (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) l x y) z) := by
      simp only [H,logIterateLowerCosetSeries,PowerSeries.coeff_mk]
      have ha : r+c-β-1+(n : ℂ)=γ+c-β-1 := by linear_combination hn
      have hb : a+b-r-1-(n : ℂ)=a+b-γ-1 := by linear_combination -hn
      rw [ha,hb]
    by_cases hk : k<K
    · rw [Finset.sum_eq_single k]
      · rw [if_pos rfl,hc k]
      · intro l hl hlk
        rw [if_neg hlk]
      · intro hk'
        exact False.elim (hk' (Finset.mem_range.mpr hk))
    · have hz : Y₄.1 (a+b-γ-1) k=0 := hK Y₄ _ k (by omega)
      rw [hz,LinearMap.zero_apply,LinearMap.zero_apply,map_zero,LinearMap.zero_apply,map_zero]
      apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg (by have := Finset.mem_range.mp hl; omega)]
  · rw [if_neg hγ]
    apply Finset.sum_eq_zero
    intro l hl
    apply exCoeff_of_forall_ne
    intro n he
    apply hγ
    exact ⟨n,by linear_combination he⟩

/-- The unique collision coefficients of the whole literal true iterate
are exactly its actual inner logarithmic mode coefficients. -/
theorem logCoeff_iterateSpectrum (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (logIterateSpectrumFun hC2 N₅ hfg₅ Y₃.1 Y₄.1 f x y z a b c β) (γ-a-b) k=
      f (Y₃.1 (γ+c-β-1) 0 (Y₄.1 (a+b-γ-1) k x y) z) := by
  classical
  unfold logIterateSpectrumFun
  rw [logCoeff_sum isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (spectrumCosets hC2 N₅ hfg₅) (fun mu _ => log_iterate_lowerCoset_hasLogExp
      hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z a b c β _)]
  simp_rw [logCoeff_lowerIterate hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₃ Y₄ f x y z a b c β]
  apply lowerSpectrum_indicator hC2 N₅ hfg₅
  intro hC hbot
  have hm := Y₄.2.mem_weight hx hy (a+b-γ-1) k
  have he : a+b-(a+b-γ-1)-1=γ := by ring
  rw [he,hbot] at hm
  have hz : Y₄.1 (a+b-γ-1) k x y=0 := (Submodule.mem_bot ℂ).mp hm
  apply hC
  rw [hz,map_zero,LinearMap.zero_apply,map_zero]

end VOA.Huang.LogAssocExpansion
