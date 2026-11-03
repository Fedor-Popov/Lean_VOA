import VOA.Huang.GenusOneFinite
import VOA.Huang.BuhlSpanningMain
import VOA.Modularity.LowestWeightExistence

/-!
# C₂ convergence for one-point intertwiner traces

The two trace-span obligations are proved from C₂-cofiniteness of the insertion
module. For irreducible ordinary insertions Buhl's theorem discharges that condition,
with only C₂-cofiniteness of the VOA. The traced module need not be irreducible.

The extension of Buhl's conclusion to every reducible ordinary insertion is exposed
separately as `OrdinaryInsertionC2`; it is not inferred from the irreducible theorem.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.Huang.FusionC2
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Buhl's module-C₂ theorem in unbundled ordinary-module form. -/
theorem moduleC2_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible) :
    ModuleC2Cofinite A.toWeakModule := by
  obtain ⟨h, hlow, hne⟩ := A.exists_isLowestWeight_of_irreducible hA
  let P : LWModule W := ⟨M₁, A, h, hlow, hne⟩
  exact BuhlSpanning.moduleC2Cofinite_of_irreducibleLW hC2 P hA

/-- Finite generation for every intertwiner with irreducible ordinary insertion. -/
theorem traceSpanFinite_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    TraceSpanFinite Y hcw :=
  traceSpanFinite_of_moduleC2 Y (moduleC2_of_irreducible hC2 hA) hcw

/-- Both trace obligations, with no remaining genus-one assumptions. -/
theorem trace_inputs_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    TraceSpanFinite Y hcw ∧ TraceDerivativeClosed Y hcw :=
  ⟨traceSpanFinite_of_irreducible hC2 hA Y hcw, traceDerivativeClosed_holds Y hcw⟩

theorem traceSubexponential_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    TraceSubexponential Y h :=
  traceSubexponential_of_fg_closed Y hcw (traceSpanFinite_of_irreducible hC2 hA Y hcw)
    (traceDerivativeClosed_holds Y hcw)

/-- Absolute convergence on the full unit disc for general intertwining operators. -/
theorem summable_trace_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h q : ℂ} (hcw : HasConformalWeight N h)
    (hq : ‖q‖ < 1) (w : M₁) :
    Summable (fun n : ℕ => ‖trace Y w (h - W.centralCharge / 24 + n) * q ^ n‖) :=
  summable_trace_of_moduleC2 Y (moduleC2_of_irreducible hC2 hA) hcw hq w

/-- Certified trace evaluation, including the conformal exponential prefactor. -/
theorem hasSum_trace_of_irreducible (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h)
    (w : M₁) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h - W.centralCharge / 24)) *
        (trace Y w (h - W.centralCharge / 24 + n) * qParam τ ^ n))
      (traceFunction Y h w τ) :=
  hasSum_trace_of_moduleC2 Y (moduleC2_of_irreducible hC2 hA) hcw w τ

/-- Remaining purely module-theoretic bridge for arbitrary reducible ordinary insertions.
For strongly rational W this follows from finite decomposition into irreducible ordinary
modules and Buhl's theorem. The decomposition and C₂ transport are not proved here. -/
def OrdinaryInsertionC2 (W : VertexOperatorAlgebra V) : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] (B : OrdVModule W E),
    ModuleC2Cofinite B.toWeakModule

/-- The residual module theorem implies both trace-span obligations for every insertion. -/
theorem trace_inputs_of_ordinaryInsertionC2 (hmod : OrdinaryInsertionC2 W)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h) :
    TraceSpanFinite Y hcw ∧ TraceDerivativeClosed Y hcw :=
  ⟨traceSpanFinite_of_moduleC2 Y (hmod M₁ A) hcw, traceDerivativeClosed_holds Y hcw⟩

theorem summable_trace_of_ordinaryInsertionC2 (hmod : OrdinaryInsertionC2 W)
    (Y : IntertwiningOperator A N N) {h q : ℂ} (hcw : HasConformalWeight N h)
    (hq : ‖q‖ < 1) (w : M₁) :
    Summable (fun n : ℕ => ‖trace Y w (h - W.centralCharge / 24 + n) * q ^ n‖) :=
  summable_trace_of_moduleC2 Y (hmod M₁ A) hcw hq w

end VOA.Huang.GenusOne
