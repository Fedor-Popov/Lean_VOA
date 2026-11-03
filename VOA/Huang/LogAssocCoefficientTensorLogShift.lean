import VOA.Huang.LogAssocCoefficientTensorPair

/-! Literal finite logarithmic evaluation of the canonical tensor modes
recovers the actual collision coefficient polynomial at every logarithm. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct
open VOA.C2Rigid.LocalInjective VOA.VHat VOA.VHat.DLM3
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)

/-- The full genuine canonical tensor logarithm pairs with the literal
collision polynomial, with no normalization or log-free assumption. -/
theorem tensorIntertwiner_logShift_pair_coefficient (f : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β γ ell : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) :
    C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW
      (⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
        coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩)
      (logShift ell (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂).1 (a+b-γ-1) 0 x y) =
      ∑' k : ℕ,ell^k * coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y := by
  let η := tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂
  let s : maximalCarrier N₁.toWeakModule N₂.toWeakModule :=
    ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0,
      coefficient_mem_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz⟩
  have hp (k : ℕ) : C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW s
      (η.1 (a+b-γ-1) k x y) =
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y :=
    tensorIntertwiner_pair_coefficient hC2 N₁ N₂ hfg₁ hfg₂ N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f z c β γ k hx hy hf hz
  obtain ⟨K,hK⟩ := η.2.logFinite x y (a+b-γ-1)
  have hc (k : ℕ) (hk : K≤k) :
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y=0 := by
    rw [← hp k,hK k hk,map_zero]
  change C2Rigid.dualPairing (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW s
    (logShift ell η.1 (a+b-γ-1) 0 x y)=_
  rw [logShift_eq_sum η.2.logFinite K hK,map_sum]
  rw [tsum_eq_sum (s := Finset.range K) (fun k hk => by
    rw [hc k (by simpa only [Finset.mem_range,not_lt] using hk),mul_zero])]
  simp only [map_smul,shc,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => congrArg (fun q => ell^k*q) (hp k)

end VOA.Huang.LogAssocCoefficientL0
