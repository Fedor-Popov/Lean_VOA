import VOA.Classification.COne.McRaeM2LogBraidedHalfPlane
import VOA.Modules.LogTensorPzPointPrecompose
import VOA.Modules.LogTensorPzPointPostcompose
import VOA.Classification.COne.McRaeM2TensorMaps

/-! # Completed evaluations along holomorphic curves of branches

* A completed iterate (resp. product) of homogeneous vectors, evaluated along
  holomorphic branch curves `u ↦ (ℓ₀(u), ℓ₂(u))` staying in `Re ℓ₀ < Re ℓ₂`
  (resp. `Re λ₂ < Re λ₁`), is holomorphic in `u`
  (`differentiableAt_completedLogIterate_comp`, `differentiableAt_completedLogProduct_comp`).
* Precomposing the outer operator by a module map on its intermediate slot is the
  same as postcomposing the inner operator (`completedLogIterate_precompose_left`,
  `completedLogProduct_precompose_right`).
* A completed iterate on a vanishing output weight space vanishes. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogBraided
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] [AddCommGroup M₆] [Module ℂ M₆]

/-- Completed iterates are holomorphic along holomorphic branch curves. -/
theorem differentiableAt_completedLogIterate_comp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {ℓ₀ ℓ₂ : ℂ → ℂ} {u : ℂ}
    (h₀ : DifferentiableAt ℂ ℓ₀ u) (h₂ : DifferentiableAt ℂ ℓ₂ u)
    (hlt : (ℓ₀ u).re < (ℓ₂ u).re) :
    DifferentiableAt ℂ (fun u => completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ (ℓ₀ u) (ℓ₂ u) c β f x y
      ⟨z,hz⟩) u := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₅ N₃ N₄ hfg₅ hfg₃ hfg₄
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  have hcurve : DifferentiableAt ℂ (fun u => (ℓ₀ u, ℓ₂ u)) u := h₀.prodMk h₂
  have hv := ((differentiableOn_iterValue hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
    K L f x y z a b c β).differentiableAt (isOpen_re_lt_pair.mem_nhds
      (show (ℓ₀ u, ℓ₂ u).1.re < (ℓ₀ u, ℓ₂ u).2.re from hlt))).comp u hcurve
  refine hv.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ v in nhds u, (ℓ₀ v).re < (ℓ₂ v).re := by
    have hc : ContinuousAt (fun v => (ℓ₂ v).re - (ℓ₀ v).re) u :=
      (Complex.continuous_re.continuousAt.comp h₂.continuousAt).sub
        (Complex.continuous_re.continuousAt.comp h₀.continuousAt)
    have := hc.eventually (isOpen_Ioi.mem_nhds (show (0:ℝ) < (ℓ₂ u).re - (ℓ₀ u).re by linarith))
    exact this.mono fun v hv => by have hv : (0:ℝ) < _ := hv; linarith
  filter_upwards [hev] with v hv
  exact (completedLogIterate_eq_iterValue hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
    (fun n k hk => hK Y₃ n k hk) (fun n l hl => hL Y₄ n l hl) hx hy hz f β hv).2

/-- Completed products are holomorphic along holomorphic branch curves. -/
theorem differentiableAt_completedLogProduct_comp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {m₁ m₂ : ℂ → ℂ} {u : ℂ}
    (h₁ : DifferentiableAt ℂ m₁ u) (h₂ : DifferentiableAt ℂ m₂ u)
    (hlt : (m₂ u).re < (m₁ u).re) :
    DifferentiableAt ℂ (fun u => completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (m₁ u) (m₂ u) a β f
      ⟨x,hx⟩ y z) u := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hcurve : DifferentiableAt ℂ (fun u => (m₁ u, m₂ u)) u := h₁.prodMk h₂
  have hopen : IsOpen {p : ℂ × ℂ | p.2.re < p.1.re} :=
    isOpen_lt (Complex.continuous_re.comp continuous_snd) (Complex.continuous_re.comp continuous_fst)
  have hv := ((differentiableOn_prodValue hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    K L f x y z a b c β).differentiableAt (hopen.mem_nhds
      (show (m₁ u, m₂ u).2.re < (m₁ u, m₂ u).1.re from hlt))).comp u hcurve
  refine hv.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ v in nhds u, (m₂ v).re < (m₁ v).re := by
    have hc : ContinuousAt (fun v => (m₁ v).re - (m₂ v).re) u :=
      (Complex.continuous_re.continuousAt.comp h₁.continuousAt).sub
        (Complex.continuous_re.continuousAt.comp h₂.continuousAt)
    have := hc.eventually (isOpen_Ioi.mem_nhds (show (0:ℝ) < (m₁ u).re - (m₂ u).re by linarith))
    exact this.mono fun v hv => by have hv : (0:ℝ) < _ := hv; linarith
  filter_upwards [hev] with v hv
  exact (completedLogProduct_eq_prodValue hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    (fun n k hk => hK Y₁ n k hk) (fun n l hl => hL Y₂ n l hl) hx hy hz f β hv).2

/-- A completed iterate on a vanishing output weight space is zero. -/
theorem completedLogIterate_eq_zero_of_bot
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ℓ₀ ℓ₂ c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : N₃.weight c)
    (hβ : N₄.weight β = ⊥) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ℓ₀ ℓ₂ c β f x y z = 0 := by
  unfold completedLogIterate completedIteratePair
  refine (tsum_congr fun γ => ?_).trans tsum_zero
  have hbot : N₄.weight β ≤ (⊥ : Submodule ℂ M₄) := by rw [hβ]
  rw [(Submodule.mem_bot ℂ).mp (hbot (pointEvaluationBlock N₅ N₃ N₄ Y₃ ℓ₂ γ c β
    (evaluatePoint N₁ N₂ N₅ Y₄ ℓ₀ x y γ) z).2), map_zero]

/-- Precomposing the outer operator on its intermediate slot equals postcomposing
the inner operator. -/
theorem completedLogIterate_precompose_left
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)
    (h : N₅.toWeakModule.Hom N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₆.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (ℓ₀ ℓ₂ c β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : N₃.weight c) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅
        (precompose h (C2Rigid.LocalInjective.weakIdentity N₃.toWeakModule) Y₃) Y₄ ℓ₀ ℓ₂ c β
        f x y z =
      completedLogIterate N₁ N₂ N₃ N₄ N₆ Y₃ (postcompose h Y₄) ℓ₀ ℓ₂ c β f x y z := by
  unfold completedLogIterate completedIteratePair
  refine tsum_congr fun γ => ?_
  rw [pointEvaluationBlock_precompose, evaluatePoint_postcompose]
  rfl

/-- Precomposing the outer operator on its second slot equals postcomposing the
inner operator. -/
theorem completedLogProduct_precompose_right
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)
    (h : N₅.toWeakModule.Hom N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (m₁ m₂ a β : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : N₁.weight a) (y : M₂) (z : M₃) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅
        (precompose (C2Rigid.LocalInjective.weakIdentity N₁.toWeakModule) h Y₁) Y₂ m₁ m₂ a β
        f x y z =
      completedLogProduct N₁ N₂ N₃ N₄ N₆ Y₁ (postcompose h Y₂) m₁ m₂ a β f x y z := by
  unfold completedLogProduct completedProductPair
  refine tsum_congr fun γ => ?_
  rw [pointEvaluationBlock_precompose, evaluatePoint_postcompose]
  rfl

end VOA.Huang.LogBraided
