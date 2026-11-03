import VOA.Huang.GenusOneEisenstein

/-!
# Analytic Eisenstein differential systems for intertwiner traces

The finite system is evaluated using absolutely convergent Cauchy products.
Its matrix entries are q-expansions in ℂ[G₂,G₄,G₆]. This is an Euler system;
no modular weight assignment or S-covariance of this particular system is asserted.
-/
namespace VOA.Huang.GenusOne
open VOA
open scoped BigOperators
universe u

/-- Evaluation of a formal Eisenstein-ring coefficient. -/
noncomputable def eisensteinEval (F : ↥GSeries) (z : ℂ) : ℂ :=
  ∑' n : ℕ, PowerSeries.coeff n (F : PowerSeries ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)

theorem summable_norm_eisenstein (F : ↥GSeries) {z : ℂ} (hz : z ∈ imGT 0) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff n (F : PowerSeries ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖) := by
  have hs := summable_of_subexponential (fun n => norm_nonneg (PowerSeries.coeff n
    (F : PowerSeries ℂ))) (GSeries_le_subexpPS F.property)
    (qRatio_pos z.im).le (qRatio_lt_one hz)
  refine hs.congr fun n => ?_
  rw [norm_mul, norm_qexp, qRatio, ← Real.exp_nat_mul]
  congr 2
  ring

theorem qEvalC_psSMul_G (F : ↥GSeries) {χ : FormalQSeries} {b z : ℂ}
    (hsupp : χ ∈ QSeriesAt b)
    (hsub : Subexponential (fun n : ℕ => ‖χ (b + n)‖)) (hz : z ∈ imGT 0) :
    qEvalC (psSMul (F : PowerSeries ℂ) χ) b z = eisensteinEval F z * qEvalC χ b z :=
  qEvalC_qConv _ χ b (QSeriesAt.support_neg hsupp) (summable_norm_eisenstein F hz)
    (summable_norm_qTerm χ b hsub hz)

variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Formal finite systems evaluate to genuine differential equations. -/
theorem eisenstein_system_analytic (S : M₁ →ₗ[ℂ] FormalQSeries) {b : ℂ}
    (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hsub : ∀ w, Subexponential (fun n : ℕ => ‖S w (b + n)‖))
    (U : Finset M₁) (B : U → U → ↥GSeries)
    (hsys : ∀ k : U, qD b (blockRestrict hsupp k.val) =
      ∑ l : U, B k l • blockRestrict hsupp l.val)
    (k : U) {z : ℂ} (hz : z ∈ imGT 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (qEvalC (S k.val) b) z =
      ∑ l : U, eisensteinEval (B k l) z * qEvalC (S l.val) b z := by
  classical
  have heq := congrArg (fun x : ↥(QSeriesAt b) => (x : FormalQSeries)) (hsys k)
  dsimp only at heq
  rw [qD_coe, Submodule.coe_sum] at heq
  change qDeriv (S k.val) = ∑ l : U, psSMul (B k l : PowerSeries ℂ) (S l.val) at heq
  rw [← qEvalC_qDeriv _ _ (hsub k.val) hz, heq]
  rw [qEvalC_sum]
  · exact Finset.sum_congr rfl fun l _ => qEvalC_psSMul_G (B k l) (hsupp l.val) (hsub l.val) hz
  · intro l _
    exact summable_qTerm_qConv _ _ b (QSeriesAt.support_neg (hsupp l.val))
      (summable_norm_eisenstein (B k l) hz) (summable_norm_qTerm _ _ (hsub l.val) hz)

/-- Every intertwiner trace with C₂-cofinite irreducible insertion belongs to an
actual finite holomorphic Eisenstein system, and all insertion values are generated
by its components over the formal Eisenstein ring. -/
theorem exists_trace_analytic_eisenstein_system (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    ∃ (U : Finset M₁) (B : U → U → ↥GSeries),
      (∀ k : U, DifferentiableOn ℂ (traceFunctionC Y h k.val) (imGT 0)) ∧
      (∀ (k : U) (z : ℂ), z ∈ imGT 0 →
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (traceFunctionC Y h k.val) z =
          ∑ l : U, eisensteinEval (B k l) z * traceFunctionC Y h l.val z) ∧
      (∀ w, ∃ c : U → ↥GSeries, blockRestrict (trace_mem_QSeriesAt Y hcw) w =
        ∑ l : U, c l • blockRestrict (trace_mem_QSeriesAt Y hcw) l.val) := by
  obtain ⟨U, B, hsys, hgen⟩ := exists_trace_eisenstein_system hC2 hA Y hcw
  exact ⟨U, B, fun k => differentiableOn_traceFunctionC_of_irreducible hC2 hA Y hcw k.val,
    fun k _ hz => eisenstein_system_analytic (trace Y) (trace_mem_QSeriesAt Y hcw)
      (traceSubexponential_of_irreducible hC2 hA Y hcw) U B hsys k hz, hgen⟩

end VOA.Huang.GenusOne
