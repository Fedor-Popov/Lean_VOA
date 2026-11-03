import VOA.Huang.LogAssocCompletedIterate
import VOA.Modules.LogTensorPzPointScaling

/-! Genuine logarithmic point evaluations on a creation slice are ordinary
power series because the specified actual creation coefficients vanish.
The remaining outer operator may have arbitrary logarithmic coefficients. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ M₄ M₅ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] {W : VertexOperatorAlgebra V}

/-- At the literal branch zero, true finite-log point blocks are the actual
zeroth logarithmic coefficient. -/
theorem pointEvaluationBlock_branch_zero
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    (pointEvaluationBlock N₁ N₂ N₃ Y 0 a b c x y : M₃)=Y.1 (a+b-c-1) 0 x y := by
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

/-- The true completed iterate on an actual creation slice is its literal
convergent power row; no vanishing of the outer logarithms is assumed. -/
theorem completedLogIterate_creation_eq_tsum
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {a c : ℂ} {x : M₁} {v : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hv : v∈N₂.weight 0) (hz : z∈N₃.weight c)
    (hlog : ∀ n k,1≤k → Y₄.1 n k x v=0)
    (hcreation : ∀ (n : ℂ),(∀ j : ℕ,n≠-1-j) → Y₄.1 n 0 x v=0)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {r : ℝ} (hr : 0<r) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ (Complex.log r) 0 c β f x v ⟨z,hz⟩=
      ∑' j : ℕ,f (Y₃.1 (a+j+c-β-1) 0 (Y₄.1 (-1-j) 0 x v) z)*(r : ℂ)^j := by
  classical
  let q := evaluatePoint N₁ N₂ N₅ Y₄ (Complex.log r) x v
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ 0 γ c β (q γ) ⟨z,hz⟩)
  have hq (γ : ℂ) : (q γ : M₅)=Complex.exp (Complex.log r*(γ-a)) • Y₄.1 (a-γ-1) 0 x v := by
    dsimp only [q]
    rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hv]
    have he := pointEvaluationBlock_fixed_cutoff N₁ N₂ N₅ Y₄ (Complex.log r)
      a 0 γ ⟨x,hx⟩ ⟨v,hv⟩ 1 (hlog (a+0-γ-1))
    simpa only [add_zero,sub_zero,Finset.sum_range_one,pow_zero,one_smul] using he
  have hinj : Function.Injective (fun j : ℕ => a+(j : ℂ)) := by
    intro i j hij
    exact_mod_cast add_left_cancel hij
  have hsupp : Function.support g⊆Set.range (fun j : ℕ => a+(j : ℂ)) := by
    intro γ hγ
    by_contra he
    have hm : Y₄.1 (a-γ-1) 0 x v=0 := by
      apply hcreation
      intro j hj
      exact he ⟨j,by linear_combination hj⟩
    have hq0 : q γ=0 := by
      apply Subtype.ext
      rw [hq,hm,smul_zero]
      rfl
    exact hγ (by simp only [g,hq0,map_zero,LinearMap.zero_apply,Submodule.coe_zero])
  change (∑' γ : ℂ,g γ)=_
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro j
  dsimp only [g]
  rw [pointEvaluationBlock_branch_zero,hq,map_smul,LinearMap.smul_apply,map_smul]
  have hm : a-(a+(j : ℂ))-1=-1-j := by ring
  have he : Complex.exp (Complex.log r*((a+(j : ℂ))-a))=(r : ℂ)^j := by
    rw [show Complex.log r*((a+(j : ℂ))-a)=(j : ℂ)*Complex.log r by ring,
      Complex.exp_nat_mul,Complex.exp_log (by exact_mod_cast hr.ne')]
  rw [hm,he,smul_eq_mul]
  ring

end VOA.Huang.LogAssocExpansion
