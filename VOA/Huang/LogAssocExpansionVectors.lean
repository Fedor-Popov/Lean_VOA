import VOA.Huang.LogAssocExpansionMain
import VOA.Huang.LogAssocConvergence
import VOA.Huang.AssocCoeffRules

/-! Absolute convergence of actual logarithmic product coefficients.
All five modules are genuine finitely generated grading-restricted generalized
modules. C2-cofiniteness supplies C1 reduction; the coupled logarithmic
derivative supplies the regular Euler equation. No ordinary-module or
L0-semisimplicity premise appears. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct VOA.Huang.MatrixCoeff
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.AssocExpansion VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules (hasLogExp_congr hasLogExp_sum)
open VOA.Huang.AssocCommutator (prodValueZ prodTermZ)
open VOA.Huang.LogAssocJacobi (summable_log_product_integerCoset)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The actual global logarithmic bound makes the full product sum finite
for arbitrary vectors, before any generalized homogeneous decomposition. -/
theorem fullCoset_eq_sum_log {K : ℕ} {Y₁ : LogModes M₁ M₅ M₄} (Y₂ : LogModes M₂ M₃ M₅)
    (hK : ∀ n k, K≤k → Y₁ n k=0) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ f x y z a b t=
      ∑ k∈Finset.range K,logProductIntegerCosetFun Y₁ Y₂ f x y z a b k 0 t := by
  unfold logProductFullCosetFun
  refine tsum_eq_sum (s := Finset.range K) fun k hk => ?_
  have hk' : K≤k := by simpa only [Finset.mem_range,not_lt] using hk
  simp only [logProductIntegerCosetFun,VOA.Huang.AssocCoeffRules.prodFunZ,
    prodValueZ,prodTermZ,prodCoeff,hK _ k hk',LinearMap.zero_apply,map_zero,
    zero_mul,tsum_zero,mul_zero]

/-- Finite genuine generalized-weight decompositions extend collision
expansions to all actual vectors and all their logarithmic coefficients. -/
theorem log_product_fullCoset_hasLogExp_all (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b : ℂ)  :
    HasLogExp overlapDomain (logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b) := by
  classical
  obtain ⟨F₁,_,hs₁⟩ := C2Rigid.exists_sum_cmp N₁.toGW x
  obtain ⟨F₂,_,hs₂⟩ := C2Rigid.exists_sum_cmp N₂.toGW y
  obtain ⟨F₃,_,hs₃⟩ := C2Rigid.exists_sum_cmp N₃.toGW z
  let G : ℂ → ℂ → ℂ → ℂ → ℂ := fun α β γ =>
    logProductFullCosetFun Y₁.1 Y₂.1 f (C2Rigid.cmp N₁.toGW α x)
      (C2Rigid.cmp N₂.toGW β y) (C2Rigid.cmp N₃.toGW γ z) a b
  have hG (α β γ : ℂ) : HasLogExp overlapDomain (G α β γ) :=
    log_product_fullCoset_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ (C2Rigid.cmp_mem N₁.toGW α x) (C2Rigid.cmp_mem N₂.toGW β y)
      (C2Rigid.cmp_mem N₃.toGW γ z) f a b
  have hE : HasLogExp overlapDomain (fun t =>
      ∑ α∈F₁,∑ β∈F₂,∑ γ∈F₃,G α β γ t) :=
    hasLogExp_sum _ fun α _ => hasLogExp_sum _ fun β _ =>
      hasLogExp_sum _ fun γ _ => hG α β γ
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  refine hasLogExp_congr (fun t ht => ?_) hE
  simp only [G,fullCoset_eq_sum_log Y₂.1 hzero]
  simp_rw [Finset.sum_comm (s := F₃) (t := Finset.range K)]
  simp_rw [Finset.sum_comm (s := F₂) (t := Finset.range K)]
  rw [Finset.sum_comm (s := F₁) (t := Finset.range K)]
  refine Finset.sum_congr rfl fun k hk => ?_
  dsimp only [logProductIntegerCosetFun,VOA.Huang.AssocCoeffRules.prodFunZ]
  simp only [← Finset.mul_sum]
  congr 1
  unfold prodValueZ
  have hsum (α β γ : ℂ) : Summable
      (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0) f
        (C2Rigid.cmp N₁.toGW α x) (C2Rigid.cmp N₂.toGW β y)
        (C2Rigid.cmp N₃.toGW γ z) (a+b) b (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f _ _ _ (a+b) b k 0 one_ne_zero (by simpa only [norm_one] using one_lt_norm ht)
  simp_rw [← Summable.tsum_finsetSum (fun γ _ => hsum _ _ γ)]
  simp_rw [← Summable.tsum_finsetSum (fun β _ => summable_sum fun γ _ => hsum _ β γ)]
  rw [← Summable.tsum_finsetSum (fun α _ => summable_sum fun β _ =>
      summable_sum fun γ _ => hsum α β γ)]
  refine tsum_congr fun n => ?_
  simp_rw [prodTermZ,prodCoeff]
  conv_rhs => rw [← hs₁,← hs₂,← hs₃]
  simp only [map_sum,LinearMap.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm (s := F₃) (t := F₂)]
  simp_rw [Finset.sum_comm (s := F₃) (t := F₁)]
  rw [Finset.sum_comm (s := F₂) (t := F₁)]

end VOA.Huang.LogAssocExpansion
