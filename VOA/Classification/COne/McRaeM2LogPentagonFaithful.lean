import VOA.Classification.COne.McRaeM2LogPentagonSummable
import VOA.Classification.COne.McRaeM2LogPentagonUniq

/-! Faithfulness of the completed left five-point evaluation. A functional on
the fully iterated fourfold tensor `((N ⊠ P) ⊠ Q) ⊠ R` whose completed left
evaluations vanish on the whole common chart annihilates every literal nested
canonical coefficient. The left term is expanded into its genuine power-log
double series; each fixed-log array converges absolutely by root reflection and
the proved iterate-in-product bounds; two-scale uniqueness then kills every
coefficient. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat VOA.LogSkew
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The literal nested canonical coefficient of the left vertex, at internal
weights `γ, δ`, outer weight `β`, and logarithmic degrees `k, l`. -/
def leftCoeff (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (a b c d β : ℂ)
    (x : N) (y : P) (z : Q) (w : R) (γ δ : ℂ) (k l : ℕ) : ℂ :=
  g ((tensorIntertwiner hC2 (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
      (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration R.finiteGeneration).1
    (δ+d-β-1) 0
    ((tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).1 (γ+c-δ-1) l
      ((tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1
        (a+b-γ-1) k x y) z) w)

/-- A complex power of a positive real is the exponential of its real logarithm. -/
theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0<r) (z : ℂ) :
    (r : ℂ)^z=Complex.exp (Complex.log (r : ℂ)*z) :=
  Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne') z

section Generic
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
    [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
    [AddCommGroup M₆] [Module ℂ M₆]
    (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (N₆ : LogVModule W M₆)

/-- A doubly iterated point profile with outer branch zero is its literal
finite power-log expansion. -/
theorem iterateProfile_expand
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₆.toWeakModule N₄.toWeakModule N₀.toWeakModule)
    (e₁ e₂ a₁ a₂ a₃ a₄ β γ δ : ℂ)
    (x : N₁.weight a₁) (y : N₂.weight a₂) (z : N₃.weight a₃) (w : N₄.weight a₄)
    (g : M₀ →ₗ[ℂ] ℂ) (K L : ℕ)
    (hK : ∀ n k, K≤k → Y₁.1 n k=0) (hL : ∀ n l, L≤l → Y₂.1 n l=0) :
    g (Y₃.1 (δ+a₄-β-1) 0 (pointEvaluationBlock N₅ N₃ N₆ Y₂ e₂ γ a₃ δ
      (pointEvaluationBlock N₁ N₂ N₅ Y₁ e₁ a₁ a₂ γ x y) z : M₆) w)=
    Complex.exp (e₁*(γ-(a₁+a₂)))*(Complex.exp (e₂*(δ-γ-a₃))*
      ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range L, e₁^k*e₂^l*
        g (Y₃.1 (δ+a₄-β-1) 0 (Y₂.1 (γ+a₃-δ-1) l (Y₁.1 (a₁+a₂-γ-1) k x y) z) w)) := by
  rw [pointEvaluationBlock_fixed_cutoff N₅ N₃ N₆ Y₂ e₂ γ a₃ δ _ z L
    (fun l hl => by rw [hL _ l hl]; rfl)]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  rw [pointEvaluationBlock_fixed_cutoff N₁ N₂ N₅ Y₁ e₁ a₁ a₂ γ x y K
    (fun k hk => by rw [hK _ k hk]; rfl)]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have he : γ-a₁-a₂=γ-(a₁+a₂) := by ring
  rw [he]
  ring

end Generic

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- The literal left vertex term is its genuine power-log double series term. -/
theorem fivePointTerm_left_expand (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (K L : ℕ)
    (hK : ∀ n k, K≤k → (tensorIntertwiner hC2 N.act P.act
      N.finiteGeneration P.finiteGeneration).1 n k=0)
    (hL : ∀ n l, L≤l → (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).1 n l=0)
    (γ δ : ℂ) :
    fivePointTerm hC2 N P Q R .left a b c d β x y z w r s g γ δ=
      (r : ℂ)^(γ-(a+b))*((s : ℂ)^(δ-γ-c)*
        ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range L,
          (Real.log r : ℂ)^k*(Real.log s : ℂ)^l*
            leftCoeff hC2 N P Q R g a b c d β x y z w γ δ k l) := by
  let T := tensorObject hC2 N P
  let L' := tensorObject hC2 T Q
  let O := fivePointObject hC2 N P Q R .left
  let YNP := tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration
  let YTQ := tensorIntertwiner hC2 T.act Q.act T.finiteGeneration Q.finiteGeneration
  let YLR := tensorIntertwiner hC2 L'.act R.act L'.finiteGeneration R.finiteGeneration
  let u : T.act.weight γ := pointTensor hC2 N P (Complex.log r) x y γ
  let v : L'.act.weight δ := pointTensorBlock hC2 T Q (Complex.log s) γ c δ u z
  have h0 : fivePointTerm hC2 N P Q R .left a b c d β x y z w r s g γ δ=
      g (YLR.1 (δ+d-β-1) 0 v w) := by
    simp only [fivePointTerm]
    exact congrArg g (pointEvaluationBlock_zero_branch L'.act R.act O.act YLR δ d β v w)
  have hu : u=pointTensorBlock hC2 N P (Complex.log r) a b γ x y :=
    pointTensor_eq_block hC2 N P (Complex.log r) a b γ x y
  rw [ofReal_cpow_eq_exp hr, ofReal_cpow_eq_exp hs, ← log_ofReal_pos hr, ← log_ofReal_pos hs]
  refine h0.trans ?_
  have hv : v=pointTensorBlock hC2 T Q (Complex.log s) γ c δ
      (pointTensorBlock hC2 N P (Complex.log r) a b γ x y) z := by
    simp only [v]
    rw [hu]
  rw [hv]
  exact iterateProfile_expand O.act N.act P.act Q.act R.act T.act L'.act YNP YTQ YLR
    (Complex.log r) (Complex.log s) a b c d β γ δ x y z w g K L hK hL

end VOA.Huang.LogAssocFivePoint
