import VOA.Huang.GenusOneC2Convergence
import VOA.Modularity.AnalyticBlock

/-!
# Holomorphic intertwiner traces

Compact-uniform convergence includes the conformal exponential prefactor. The
complex-plane extension agrees with `traceFunction` on the upper half-plane.
No modular transformation is assumed in these analytic results.
-/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u

/-- The full summand, including the conformal prefactor, in the complex variable. -/
noncomputable def fullQTerm (χ : FormalQSeries) (b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * b) * qTerm χ b n z

/-- Subexponential q-series converge uniformly on every compact subset of the
upper half-plane, including the possibly complex conformal exponent. -/
theorem tendstoUniformlyOn_fullQTerm (χ : FormalQSeries) (b : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (b + n)‖))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ imGT 0) :
    TendstoUniformlyOn (fun m z => ∑ n ∈ Finset.range m, fullQTerm χ b n z)
      (qEvalC χ b) Filter.atTop K := by
  obtain ⟨c, hc, hcz⟩ := hK.exists_forall_le' Complex.continuous_im.continuousOn hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun z : ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * b)) K by fun_prop)
  have hr0 := qRatio_pos (c / 2)
  have hr1 := qRatio_lt_one (show 0 < c / 2 by linarith)
  have hsum : Summable (fun n : ℕ => ‖χ (b + n)‖ * qRatio (c / 2) ^ n) :=
    summable_of_subexponential (fun n => norm_nonneg _) hsub hr0.le hr1
  have ht : (fun z => ∑' n, fullQTerm χ b n z) = qEvalC χ b := by
    funext z
    exact tsum_mul_left
  rw [← ht]
  refine tendstoUniformlyOn_tsum_nat (hsum.mul_left (max C 0)) ?_
  intro n z hz
  rw [fullQTerm, norm_mul, qTerm, norm_mul]
  have hq := norm_qexp_le (show z ∈ imGT (c / 2) from
    lt_of_lt_of_le (by linarith) (hcz z hz)) n
  exact mul_le_mul (le_trans (hC z hz) (le_max_left _ _))
    (mul_le_mul_of_nonneg_left hq (norm_nonneg _)) (by positivity) (le_max_right _ _)

variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Complex-plane expression; only its restriction to `imGT 0` is used. -/
noncomputable def traceFunctionC (Y : IntertwiningOperator A N N) (h : ℂ)
    (w : M₁) : ℂ → ℂ := qEvalC (trace Y w) (h - W.centralCharge / 24)

@[simp] theorem traceFunctionC_coe (Y : IntertwiningOperator A N N) (h : ℂ)
    (w : M₁) (τ : UpperHalfPlane) :
    traceFunctionC Y h w (τ : ℂ) = traceFunction Y h w τ :=
  qEvalC_coe _ _ _

/-- Holomorphy for a C₂-cofinite insertion module. -/
theorem differentiableOn_traceFunctionC_of_moduleC2 (Y : IntertwiningOperator A N N)
    {h : ℂ} (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hcw : HasConformalWeight N h) (w : M₁) :
    DifferentiableOn ℂ (traceFunctionC Y h w) (imGT 0) :=
  differentiableOn_qEvalC _ _ (traceSubexponential_of_fg_closed Y hcw
    (traceSpanFinite_of_moduleC2 Y hAC2 hcw) (traceDerivativeClosed_holds Y hcw) w)

/-- Holomorphy for irreducible insertions over a C₂-cofinite VOA. -/
theorem differentiableOn_traceFunctionC_of_irreducible (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) :
    DifferentiableOn ℂ (traceFunctionC Y h w) (imGT 0) :=
  differentiableOn_traceFunctionC_of_moduleC2 Y (moduleC2_of_irreducible hC2 hA) hcw w

/-- Compact-uniform convergence of the actual trace summands. -/
theorem tendstoUniformlyOn_trace_of_irreducible (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ imGT 0) :
    TendstoUniformlyOn (fun m z => ∑ n ∈ Finset.range m,
      fullQTerm (trace Y w) (h - W.centralCharge / 24) n z)
      (traceFunctionC Y h w) Filter.atTop K :=
  tendstoUniformlyOn_fullQTerm _ _ (traceSubexponential_of_irreducible hC2 hA Y hcw w) hK hKU

/-- The derivative is the evaluation of the formal Euler derivative. -/
theorem deriv_traceFunctionC_of_irreducible (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (traceFunctionC Y h w) z =
      2 * (Real.pi : ℂ) * Complex.I *
        qEvalC (qDeriv (trace Y w)) (h - W.centralCharge / 24) z :=
  deriv_qEvalC _ _ (traceSubexponential_of_irreducible hC2 hA Y hcw w) hz

end VOA.Huang.GenusOne
