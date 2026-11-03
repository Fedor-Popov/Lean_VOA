import VOA.Huang.LogAssocExpansionVectors
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

/-- Actual full logarithmic product values are trilinear on the overlap:
finite input sums commute with the genuinely convergent integer cosets. -/
theorem fullCoset_sum_inputs (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ) 
    {I J H : Type*} (F₁ : Finset I) (F₂ : Finset J) (F₃ : Finset H)
    (X : I → M₁) (Y : J → M₂) (Z : H → M₃)
    {t : ℂ} (ht : t∈VOA.Huang.AssocExpansion.overlapDomain) :
    (∑ i∈F₁,∑ j∈F₂,∑ h∈F₃,logProductFullCosetFun Y₁.1 Y₂.1 f (X i) (Y j) (Z h) a b t)=
      logProductFullCosetFun Y₁.1 Y₂.1 f (∑ i∈F₁,X i) (∑ j∈F₂,Y j) (∑ h∈F₃,Z h) a b t := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  simp only [fullCoset_eq_sum_log Y₂.1 hzero]
  simp_rw [Finset.sum_comm (s := F₃) (t := Finset.range K)]
  simp_rw [Finset.sum_comm (s := F₂) (t := Finset.range K)]
  rw [Finset.sum_comm (s := F₁) (t := Finset.range K)]
  refine Finset.sum_congr rfl fun k hk => ?_
  dsimp only [logProductIntegerCosetFun,VOA.Huang.AssocCoeffRules.prodFunZ]
  simp only [← Finset.mul_sum]
  congr 1
  unfold prodValueZ
  have hsum (α : I) (β : J) (γ : H) : Summable
      (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0) f
        (X α) (Y β)
        (Z γ) (a+b) b (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f _ _ _ (a+b) b k 0 one_ne_zero (by simpa only [norm_one] using one_lt_norm ht)
  simp_rw [← Summable.tsum_finsetSum (fun γ _ => hsum _ _ γ)]
  simp_rw [← Summable.tsum_finsetSum (fun β _ => summable_sum fun γ _ => hsum _ β γ)]
  rw [← Summable.tsum_finsetSum (fun α _ => summable_sum fun β _ =>
      summable_sum fun γ _ => hsum α β γ)]
  refine tsum_congr fun n => ?_
  simp_rw [prodTermZ,prodCoeff]
  simp only [map_sum,LinearMap.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm (s := F₃) (t := F₂)]
  simp_rw [Finset.sum_comm (s := F₃) (t := F₁)]
  rw [Finset.sum_comm (s := F₂) (t := F₁)]

/-- Scalar multiplication commutes with both actual mode-coset sums. -/
theorem fullCoset_smul_left (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (s a b t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ f (s•x) y z a b t=
      s*logProductFullCosetFun Y₁ Y₂ f x y z a b t := by
  unfold logProductFullCosetFun
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hval : prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f (s•x) y z (a+b) b
      (1+Complex.exp t) 1=
      s*prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x y z (a+b) b
        (1+Complex.exp t) 1 := by
    unfold prodValueZ
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [prodTermZ,prodCoeff,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  unfold logProductIntegerCosetFun VOA.Huang.AssocCoeffRules.prodFunZ
  rw [hval]
  ring

/-- Scalar multiplication commutes with both actual mode-coset sums. -/
theorem fullCoset_smul_right (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (s a b t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ f x (s•y) z a b t=
      s*logProductFullCosetFun Y₁ Y₂ f x y z a b t := by
  unfold logProductFullCosetFun
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hval : prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x (s•y) z (a+b) b
      (1+Complex.exp t) 1=
      s*prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x y z (a+b) b
        (1+Complex.exp t) 1 := by
    unfold prodValueZ
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [prodTermZ,prodCoeff,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  unfold logProductIntegerCosetFun VOA.Huang.AssocCoeffRules.prodFunZ
  rw [hval]
  ring

/-- Scalar multiplication commutes with both actual mode-coset sums. -/
theorem fullCoset_smul_third (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (s a b t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ f x y (s•z) a b t=
      s*logProductFullCosetFun Y₁ Y₂ f x y z a b t := by
  unfold logProductFullCosetFun
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hval : prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x y (s•z) (a+b) b
      (1+Complex.exp t) 1=
      s*prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x y z (a+b) b
        (1+Complex.exp t) 1 := by
    unfold prodValueZ
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [prodTermZ,prodCoeff,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  unfold logProductIntegerCosetFun VOA.Huang.AssocCoeffRules.prodFunZ
  rw [hval]
  ring

/-- Actual additivity on the convergent overlap. -/
theorem fullCoset_add_left (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x x' : M₁) (y : M₂) (z : M₃) (a b : ℂ)  {t : ℂ} (ht : t∈VOA.Huang.AssocExpansion.overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 f (x+x') y z a b t=
      logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b t+
        logProductFullCosetFun Y₁.1 Y₂.1 f x' y z a b t := by
  have hh := fullCoset_sum_inputs hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f a b (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset Unit) (Finset.univ : Finset Unit) ![x,x'] (fun _ => y) (fun _ => z) ht
  simpa only [Fin.sum_univ_two,Fintype.sum_unique,Matrix.cons_val_zero,Matrix.cons_val_one] using hh.symm

/-- Actual additivity on the convergent overlap. -/
theorem fullCoset_add_right (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y y' : M₂) (z : M₃) (a b : ℂ)  {t : ℂ} (ht : t∈VOA.Huang.AssocExpansion.overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 f x (y+y') z a b t=
      logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b t+
        logProductFullCosetFun Y₁.1 Y₂.1 f x y' z a b t := by
  have hh := fullCoset_sum_inputs hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f a b (Finset.univ : Finset Unit) (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset Unit) (fun _ => x) ![y,y'] (fun _ => z) ht
  simpa only [Fin.sum_univ_two,Fintype.sum_unique,Matrix.cons_val_zero,Matrix.cons_val_one] using hh.symm

end VOA.Huang.LogAssocExpansion
