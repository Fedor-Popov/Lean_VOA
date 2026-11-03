import VOA.Huang.LogAssocCoefficientL0Weight
import VOA.Huang.LogAssocCoefficientL0Defect
import VOA.Classification.COne.McRaeM2TensorUniversal
import VOA.Modules.LogTensorArDualPairing
import VOA.Modules.LogTensorPzNilCovariance

/-! Every actual canonical tensor logarithmic coefficient pairs with the
literal full-logarithmic collision coefficient. The source Jordan defect
and genuine contragredient pairing supply the exact factorial recurrence. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct
open VOA.C2Rigid.LocalInjective VOA.VHat VOA.VHat.DLM3
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)

/-- Actual tensor modes pair with the exact powers of the full collision Jordan defect. -/
theorem tensorIntertwiner_factorial_pair (k : ℕ) (a b γ n : ℂ) (hγ : γ=a+b-n-1)
    (x : M₁) (y : M₂) (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (s : maximalCarrier N₁.toWeakModule N₂.toWeakModule)
    (hs : s∈(tensorDual hC2 N₁ N₂ hfg₁ hfg₂).weight γ) :
    (k.factorial:ℂ) * C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW s
      ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 n k x y) =
      ((coefficientDefect N₁ N₂ γ)^k) (s : BilinearDual (M₁ := M₁) (M₂ := M₂)) x y := by
  let S := tensorDual hC2 N₁ N₂ hfg₁ hfg₂
  let η := tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂
  induction k generalizing x y s with
  | zero =>
    simp only [Nat.factorial_zero,Nat.cast_one,one_mul,pow_zero,Module.End.one_apply]
    rw [tensorIntertwiner_logZero hC2 N₁ N₂ hfg₁ hfg₂ n,
      pair_baseModes N₁ N₂ S (tensorInclusion hC2 N₁ N₂ hfg₁ hfg₂).1 n hx hy hs,if_pos hγ]
    rfl
  | succ k ih =>
    have hnilS : S.L0nil s∈S.weight γ := S.L0nil_mem_weight hs
    have hnS : (S.L0nil s : BilinearDual (M₁ := M₁) (M₂ := M₂)) =
        (dualL0 N₁ N₂-γ • 1) (s : BilinearDual (M₁ := M₁) (M₂ := M₂)) := by
      rw [S.L0nil_apply_of_mem hs]
      change (L0 (maximalWeakModule N₁.toWeakModule N₂.toWeakModule) s : BilinearDual (M₁ := M₁) (M₂ := M₂))-
        γ • (s : BilinearDual (M₁ := M₁) (M₂ := M₂))=_
      erw [compatible_L0_coe N₁ N₂ (maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule)]
      rfl
    have hr := congrArg
      (fun F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] C2Rigid.RestrictedDual S.toGW => C2Rigid.dualPairing S.toGW s (F x y))
      (nilDefect_logCoeff N₁ N₂ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) η n k)
    simp only [nilDefect,bilinearDefect_apply,LinearMap.smul_apply,map_sub,map_smul,smul_eq_mul] at hr
    erw [Ar.pair_contra_L0nil S] at hr
    have hf : ((k+1).factorial:ℂ)=(k.factorial:ℂ)*((k:ℂ)+1) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    change ((k+1).factorial:ℂ)*C2Rigid.dualPairing S.toGW s (η.1 n (k+1) x y)=_
    rw [hf,mul_assoc,← hr,mul_sub,mul_sub]
    rw [ih x y hx hy (S.L0nil s) hnilS,
      ih (N₁.L0nil x) y (N₁.L0nil_mem_weight hx) hy s hs,
      ih x (N₂.L0nil y) hx (N₂.L0nil_mem_weight hy) s hs,hnS]
    exact (coefficientDefect_pow_step N₁ N₂ γ k (s : BilinearDual (M₁ := M₁) (M₂ := M₂)) x y).symm

variable {M₃ M₄ M₅ : Type u}
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
  (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ)

/-- The genuine collision Ward identity recovers every coefficient by exact defect powers. -/
theorem coefficientDefect_pow_zero (k : ℕ) :
    ((coefficientDefect N₁ N₂ γ)^k)
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0) =
      (k.factorial:ℂ) • coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k := by
  have hrec (j : ℕ) : coefficientDefect N₁ N₂ γ
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ j) =
      ((j:ℂ)+1) • coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ (j+1) := by
    have hw := coefficient_L0_Ward hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ j
    rw [coefficientDefect,LinearMap.sub_apply,LinearMap.sub_apply,hw]
    abel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih,map_smul,hrec,smul_smul,Nat.factorial_succ]
    push_cast
    congr 1
    ring

/-- Every canonical tensor logarithmic mode pairs with the literal genuine
collision coefficient at the same logarithmic degree. -/
theorem tensorIntertwiner_pair_coefficient (k : ℕ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) :
    C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW
      (⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
        coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩)
      ((tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 (a+b-γ-1) k x y) =
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y := by
  have hp := tensorIntertwiner_factorial_pair hC2 N₁ N₂ hfg₁ hfg₂ k a b γ (a+b-γ-1)
    (by ring) x y hx hy
    (⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
      coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩)
    (coefficient_mem_maximal_weight hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f z c β γ 0 hf hz)
  rw [coefficientDefect_pow_zero hC2 N₁ N₂ hfg₁ hfg₂ N₃ N₄ N₅ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k] at hp
  simp only [LinearMap.smul_apply,smul_eq_mul] at hp
  exact (mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k : (k.factorial:ℂ)≠0)) hp

end
end VOA.Huang.LogAssocCoefficientL0
