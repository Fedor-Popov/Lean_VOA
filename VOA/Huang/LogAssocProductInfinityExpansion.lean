import VOA.Huang.LogAssocIterateCoefficients
import VOA.Huang.LogHuangODEProductMain

/-! The literal logarithmic product at infinity, with z1=exp(-sigma),
z2=1 and the chosen logarithm -sigma. Actual lower spectrum rows retain
every outer logarithmic degree in a convergent Frobenius expansion. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.Huang.LogHuangODEProduct
open VOA.Huang.LogHuangODEIterPoint VOA.Huang.LogRemovalCoeff
open VOA.Huang.FrobeniusLog VOA.Huang.AssocExpansion
open VOA.Huang.AssocCoeffRules (hasLogExp_congr hasLogExp_sum)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- A literal convergent monomial-log row is Frobenius on the entire half-plane. -/
theorem hasLogExp_monomial_psEval_halfPlane {G : PowerSeries ℂ} (hG : G∈SubexpPS)
    (lam : ℂ) (k : ℕ) :
    HasLogExp halfPlane (fun t => t^k*Complex.exp (lam*t)*psEval G (Complex.exp t)) := by
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

/-- The literal source/product coefficient series along a true lower intermediate row. -/
noncomputable def productInfinitySeries
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b c β r : ℂ) (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => f (Y₁ (a+r-β-1+n) k x (Y₂ (b+c-r-1-n) 0 y z))

/-- The actual full outer logarithmic product on that genuine lower row. -/
noncomputable def productInfinityRow
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b c β r σ : ℂ) : ℂ :=
  ∑' k : ℕ,(-σ)^k*Complex.exp ((a+r-β)*σ)*
    psEval (productInfinitySeries Y₁ Y₂ f x y z a b c β r k) (Complex.exp σ)

/-- The true global outer Jordan bound makes the full logarithmic sum finite. -/
theorem productInfinityRow_eq_sum_log {K : ℕ} {Y₁ : LogModes M₁ M₅ M₄}
    (Y₂ : LogModes M₂ M₃ M₅) (hK : ∀ n k,K≤k → Y₁ n k=0)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β r σ : ℂ) :
    productInfinityRow Y₁ Y₂ f x y z a b c β r σ=
      ∑ k∈Finset.range K,(-σ)^k*Complex.exp ((a+r-β)*σ)*
        psEval (productInfinitySeries Y₁ Y₂ f x y z a b c β r k) (Complex.exp σ) := by
  unfold productInfinityRow
  apply tsum_eq_sum
  intro k hk
  have hkl : K≤k := by simpa only [Finset.mem_range,not_lt] using hk
  have hzero : productInfinitySeries Y₁ Y₂ f x y z a b c β r k=0 := by
    ext n
    simp [productInfinitySeries,hK _ k hkl]
  simp [hzero,psEval]

/-- Actual C2 convergence proves each literal row is subexponential. -/
theorem productInfinitySeries_mem (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β r : ℂ) (k : ℕ) :
    productInfinitySeries Y₁.1 Y₂.1 f x y z a b c β r k∈SubexpPS := by
  apply subexp_of_summable_unitDisc
  intro t ht
  simpa only [productInfinitySeries,PowerSeries.coeff_mk] using
    summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f x y z (a+r-β-1) (b+c-r-1) k 0 ht

/-- The genuine entire logarithmic product row is Frobenius on the whole half-plane. -/
theorem productInfinityRow_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β r : ℂ) :
    HasLogExp halfPlane (productInfinityRow Y₁.1 Y₂.1 f x y z a b c β r) := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hF (k : ℕ) : HasLogExp halfPlane (fun σ => (-σ)^k*Complex.exp ((a+r-β)*σ)*
      psEval (productInfinitySeries Y₁.1 Y₂.1 f x y z a b c β r k) (Complex.exp σ)) := by
    have H := hasLogExp_smul ((-1:ℂ)^k)
      (hasLogExp_monomial_psEval_halfPlane (productInfinitySeries_mem hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β r k) (a+r-β) k)
    refine hasLogExp_congr (fun σ _ => ?_) H
    rw [show -σ=(-1:ℂ)*σ by ring,mul_pow]
    ring
  refine hasLogExp_congr (fun σ _ => (productInfinityRow_eq_sum_log Y₂.1
    (fun n k hk => hK Y₁ n k hk) f x y z a b c β r σ).symm) (hasLogExp_sum _ (fun k _ => hF k))

end VOA.Huang.LogAssocExpansion
