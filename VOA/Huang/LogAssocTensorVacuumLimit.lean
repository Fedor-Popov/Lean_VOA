import VOA.Huang.LogAssocCreationLimit
import VOA.Huang.LogHuangODEIterateMain

/-! The constant term of a genuine convergent logarithmic iterate on an
actual creation slice is the zeroth mode of the point-one product. Every
remaining logarithmic point coefficient is kept throughout the limit. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz Filter Topology
open VOA.Huang.LogHuangODEIterate
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ M₄ M₅ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] {W : VertexOperatorAlgebra V}

/-- True C2 logarithmic convergence and a literal creation-slice point
identity determine the actual constant mode, with no ordinary-module premise. -/
theorem creation_constant_of_completed_point_identity (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    {a c : ℂ} {x : M₁} {v : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hv : v∈N₂.weight 0) (hz : z∈N₃.weight c)
    (hlog : ∀ n k,1≤k → Y₄.1 n k x v=0)
    (hcreation : ∀ (n : ℂ),(∀ j : ℕ,n≠-1-j) → Y₄.1 n 0 x v=0)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ)
    (heq : ∀ (r : ℝ),0<r → r<1 →
      completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ (Complex.log r) 0 c β f x v ⟨z,hz⟩=
        f (pointEvaluationBlock N₁ N₃ N₄ Y (Complex.log (1+(r : ℂ))) a c β ⟨x,hx⟩ ⟨z,hz⟩)) :
    f (Y₃.1 (a+c-β-1) 0 (Y₄.1 (-1) 0 x v) z)=f (Y.1 (a+c-β-1) 0 x z) := by
  let A : ℕ → ℂ := fun j => f (Y₃.1 (a+j+c-β-1) 0 (Y₄.1 (-1-j) 0 x v) z)
  have hs : Summable (fun j : ℕ => A j*(1/2 : ℂ)^j) := by
    have hh := summable_log_iterate_series hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₃ Y₄ f x v z (a+c-β-1) (-1) 0 0 (t := 1/2) (by norm_num)
    refine hh.congr fun j => ?_
    dsimp only [A]
    congr 2
    ring
  have hleft := tendsto_creation_tsum_const A hs
  let K := pointLogCutoff N₁ N₃ N₄ a c β
  let C : ℕ → ℂ := fun k => f (Y.1 (a+c-β-1) k x z)
  have hK : 0<K := by dsimp only [K,pointLogCutoff]; omega
  have hright := tendsto_logPointPolynomial_oneAdd K hK (β-a-c) C
  have hpoint (r : ℝ) :
      f (pointEvaluationBlock N₁ N₃ N₄ Y (Complex.log (1+(r : ℂ))) a c β ⟨x,hx⟩ ⟨z,hz⟩)=
        Complex.exp (Complex.log (1+(r : ℂ))*(β-a-c))*
          ∑ k∈Finset.range K,(Complex.log (1+(r : ℂ)))^k*C k := by
    rw [pointEvaluationBlock_fixed_cutoff N₁ N₃ N₄ Y _ a c β ⟨x,hx⟩ ⟨z,hz⟩ K
      (fun k hk => pointLogCutoff_vanish N₁ N₃ N₄ Y a c β hx hz hk)]
    rw [map_smul,map_sum]
    simp only [map_smul,smul_eq_mul,C]
  have hevent : (fun r : ℝ => ∑' j : ℕ,A j*(r : ℂ)^j)=ᶠ[𝓝[>] 0]
      (fun r : ℝ => Complex.exp (Complex.log (1+(r : ℂ))*(β-a-c))*
        ∑ k∈Finset.range K,(Complex.log (1+(r : ℂ)))^k*C k) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ)<1 by norm_num)] with r hr
    have hh := completedLogIterate_creation_eq_tsum N₁ N₂ N₃ N₄ N₅ Y₃ Y₄
      hx hv hz hlog hcreation f β hr.1
    exact hh.symm.trans ((heq r hr.1 hr.2).trans (hpoint r))
  have hconst := tendsto_nhds_unique (hleft.congr' hevent) hright
  simpa only [A,C,Nat.cast_zero,add_zero,sub_zero] using hconst

end VOA.Huang.LogAssocExpansion
