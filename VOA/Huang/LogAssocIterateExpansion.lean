import VOA.Huang.LogAssocLowerSpectrum
import VOA.Huang.LogHuangODEIterateMain

/-! The genuine logarithmic iterate on each actual lower spectrum row has
an honest convergent logarithmic Frobenius expansion. All inner logarithms
remain in the literal operator series. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.LogHuangODEIterate
open VOA.Huang.LogHuangODEIterPoint VOA.Huang.LogRemovalCoeff
open VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion
open VOA.Huang.AssocCoeffRules (hasLogExp_congr)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- An actual convergent scalar power series with a finite genuine log power
is a logarithmic Frobenius function. -/
theorem hasLogExp_monomial_psEval {G : PowerSeries ℂ} (hG : G∈SubexpPS) (lam : ℂ) (k : ℕ) :
    HasLogExp overlapDomain (fun t => t^k*Complex.exp (lam*t)*psEval G (Complex.exp t)) := by
  let p : ℕ → Polynomial ℂ := fun n => Polynomial.monomial k (PowerSeries.coeff n G)
  have hp : LogGood p := by
    refine ⟨⟨k,fun n => Polynomial.natDegree_monomial_le _⟩,?_⟩
    intro l
    by_cases hl : l=k
    · subst l
      simpa only [p,Polynomial.coeff_monomial,ite_true] using (mem_subexpPS.mp hG)
    · have he : (fun n => ‖(p n).coeff l‖)=(fun _ => (0 : ℝ)) := by
        funext n
        simp [p,Polynomial.coeff_monomial,hl,Ne.symm hl]
      rw [he]
      exact subexponential_zero
  refine ⟨LogExp.single lam p hp,fun t ht => ?_⟩
  rw [LogExp.eval_single]
  dsimp only
  unfold logFun psEval
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [p,Polynomial.eval_monomial,Complex.exp_add,add_mul,Complex.exp_nat_mul]
  ring

/-- The literal coefficient series along one actual lower intermediate weight row. -/
noncomputable def logIterateLowerCosetSeries
    (Y₃ : LogModes M₅ M₃ M₄) (Y₄ : LogModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (α₁ α₂ α₃ β r : ℂ) (l : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    f (Y₃ (r+α₃-β-1+n) 0 (Y₄ (α₁+α₂-r-1-n) l x y) z)

/-- Every logarithmic degree in the genuine iterate is retained on this lower row. -/
noncomputable def logIterateLowerCosetFun
    (Y₃ : LogModes M₅ M₃ M₄) (Y₄ : LogModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (α₁ α₂ α₃ β r t : ℂ) : ℂ :=
  ∑' l : ℕ,t^l*Complex.exp ((r-α₁-α₂)*t)*
    psEval (logIterateLowerCosetSeries Y₃ Y₄ f x y z α₁ α₂ α₃ β r l) (Complex.exp t)

/-- Actual finite generation supplies a genuine finite logarithmic sum. -/
theorem lowerIterate_eq_sum_log {K : ℕ}
    (Y₃ : LogModes M₅ M₃ M₄) {Y₄ : LogModes M₁ M₂ M₅}
    (hK : ∀ n l,K≤l → Y₄ n l=0)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β r t : ℂ) :
    logIterateLowerCosetFun Y₃ Y₄ f x y z α₁ α₂ α₃ β r t=
      ∑ l∈Finset.range K,t^l*Complex.exp ((r-α₁-α₂)*t)*
        psEval (logIterateLowerCosetSeries Y₃ Y₄ f x y z α₁ α₂ α₃ β r l) (Complex.exp t) := by
  unfold logIterateLowerCosetFun
  apply tsum_eq_sum
  intro l hl
  have hkl : K≤l := by simpa only [Finset.mem_range,not_lt] using hl
  have hzero : logIterateLowerCosetSeries Y₃ Y₄ f x y z α₁ α₂ α₃ β r l=0 := by
    ext n
    simp [logIterateLowerCosetSeries,hK _ l hkl]
  simp [hzero,psEval]

/-- The actual true logarithmic iterate row has a genuine convergent
Frobenius expansion, for arbitrary vectors and outside functional. -/
theorem log_iterate_lowerCoset_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (α₁ α₂ α₃ β r : ℂ) :
    HasLogExp overlapDomain (logIterateLowerCosetFun Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r) := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  have hG (l : ℕ) : logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r l∈SubexpPS := by
    apply subexp_of_summable_unitDisc
    intro t ht
    simpa only [logIterateLowerCosetSeries,PowerSeries.coeff_mk] using
      summable_log_iterate hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
        f x y z (r+α₃-β-1) (α₁+α₂-r-1) 0 l ht
  refine hasLogExp_congr (fun t _ => (lowerIterate_eq_sum_log Y₃.1
    (fun n l hl => hK Y₄ n l hl) f x y z α₁ α₂ α₃ β r t).symm) ?_
  exact VOA.Huang.AssocCoeffRules.hasLogExp_sum _ fun l _ =>
    hasLogExp_monomial_psEval (hG l) (r-α₁-α₂) l

end VOA.Huang.LogAssocExpansion
