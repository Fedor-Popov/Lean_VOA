import VOA.Huang.LogAssocJacobi

/-! Absolute convergence of actual logarithmic product coefficients.
All five modules are genuine finitely generated grading-restricted generalized
modules. C2-cofiniteness supplies C1 reduction; the coupled logarithmic
derivative supplies the regular Euler equation. No ordinary-module or
L0-semisimplicity premise appears. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocJacobi
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct
open VOA.Huang.AssocCommutator VOA.Huang.MatrixCoeff
open VOA.Huang.LogHuangODEConvergence
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Every actual integer coset of every logarithmic product coefficient
converges, with no homogeneous-vector or one-coset assumption. -/
theorem summable_log_product_integerCoset (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (S ν : ℂ) (k l : ℕ)
    {z₁ z₂ : ℂ} (h₂ : z₂≠0) (h₁₂ : ‖z₂‖<‖z₁‖) :
    Summable (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z S ν z₁ z₂) := by
  obtain ⟨R,hR⟩ := Y₂.2.truncation y z ν
  let K := R.toNat
  have hb : IsBase (fun n => Y₂.1 n l) y z (ν+K) := by
    intro j
    have hj := hR ((K+j+1 : ℕ) : ℤ) (by dsimp [K]; omega) l
    convert hj using 1
    push_cast
    ring
  have h₁ : z₁≠0 := by
    intro he
    rw [he,norm_zero] at h₁₂
    exact (not_lt_of_ge (norm_nonneg z₂)) h₁₂
  have ht : ‖z₂/z₁‖<1 := by
    rw [norm_div,div_lt_one (norm_pos_iff.mpr h₁)]
    exact h₁₂
  let a : ℂ := S-(ν+K)
  let b : ℂ := ν+K
  have hs := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f x y z a b k l ht
  have hh := summable_log_coset_twoVar h₂ h₁₂ hs (-a-1) (-b-1) 0 0
  have hnat : Summable fun n : ℕ =>
      prodCoeff (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z
        (S-(ν+K)+n) (ν+K-n) * z₁^(-(S-(ν+K)+n)-1) * z₂^(-(ν+K-n)-1) := by
    have hh' : Summable fun n : ℕ =>
        f (Y₁.1 (a+n) k x (Y₂.1 (b-n) l y z))*z₁^((-a-1)-n)*z₂^((-b-1)+n) := by
      simpa only [pow_zero,mul_one] using hh.of_norm
    refine hh'.congr fun n => ?_
    simp only [prodCoeff,a,b]
    have he₁ : (-(S-(ν+(K : ℂ)))-1)-(n : ℂ)=-(S-(ν+K)+n)-1 := by ring
    have he₂ : (-(ν+(K : ℂ))-1)+(n : ℂ)=-(ν+K-n)-1 := by ring
    rw [he₁,he₂]
  have hshift := summable_prodTermZ_shift_iff
    (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z S ν z₁ z₂ (K : ℤ)
  simp only [Int.cast_natCast] at hshift
  exact hshift.mp (summable_prodTermZ_of_base f x z₁ z₂ hb hnat)

end VOA.Huang.LogAssocJacobi
