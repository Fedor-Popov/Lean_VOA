import VOA.Huang.GenusOneRecursion
import VOA.Modularity.BlockGrowth

/-!
# Convergence reduction for one-point intertwiner traces

The analytic argument of `BlockGrowth` is generalized to an arbitrary linear source.
The two algebraic obligations are finite generation of the trace span over `SubexpPS`
and closure under `qDeriv`.  These are distinct from mere finiteness of fusion rules.

For vertex-operator insertions both obligations are discharged using the existing Zhu
block theorem.  For general intertwiner insertions they remain explicit Props; the
source for their intended C₂-cofinite module version is Miyamoto, arXiv:math/0010180,
§§3–4, and Huang, arXiv:math/0303049, §§2–3. No assertion that they hold
unconditionally for arbitrary ordinary modules is made.
-/

namespace VOA.Huang.GenusOne

open VOA
open scoped BigOperators

universe u

section DifferentialSpan
variable {E : Type u} [AddCommGroup E] [Module ℂ E]
  {S : E →ₗ[ℂ] FormalQSeries} {hbase : ℂ}

/-- Finite generation plus derivative closure produces an actual finite matrix system. -/
theorem exists_system_of_fg_closed (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hfg : (blockSpanS hsupp).FG)
    (hclosed : ∀ z ∈ blockSpanS hsupp, qD hbase z ∈ blockSpanS hsupp) :
    ∃ (g : ℕ) (y : Fin g → ↥(QSeriesAt hbase)) (B : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD hbase (y k) = ∑ l, B k l • y l) ∧
      (∀ v : E, ∃ c : Fin g → ↥SubexpPS,
        blockRestrict hsupp v = ∑ l, c l • y l) := by
  classical
  obtain ⟨g, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    hfg
  have hmemy : ∀ k : Fin g, y k ∈ blockSpanS hsupp := by
    intro k
    rw [← hy]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hA : ∀ k : Fin g, ∃ c : Fin g → ↥SubexpPS, ∑ l, c l • y l = qD hbase (y k) := by
    intro k
    refine (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp ?_
    rw [hy]
    exact hclosed _ (hmemy k)
  choose A hAeq using hA
  refine ⟨g, y, A, fun k => (hAeq k).symm, fun v => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp
    (by rw [hy]; exact blockRestrict_mem_blockSpanS hsupp v)
  exact ⟨c, hc.symm⟩

/-- Analytic growth depends only on the finite differential span, not on the source being V. -/
theorem subexponential_of_fg_closed (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hfg : (blockSpanS hsupp).FG)
    (hclosed : ∀ z ∈ blockSpanS hsupp, qD hbase z ∈ blockSpanS hsupp) (v : E) :
    Subexponential (fun n : ℕ => ‖S v (hbase + (n : ℂ))‖) := by
  classical
  obtain ⟨g, y, A, hsys, hgen⟩ := exists_system_of_fg_closed hsupp hfg hclosed
  set z : Fin g → ℕ → ℂ := fun k n => ((y k : ↥(QSeriesAt hbase)) : FormalQSeries)
    (hbase + (n : ℂ)) with hz
  set a : Fin g → Fin g → ℕ → ℂ := fun k l j =>
    PowerSeries.coeff j ((A k l : ↥SubexpPS) : PowerSeries ℂ) with ha
  have haSub : ∀ k l, Subexponential (fun j => ‖a k l j‖) := fun k l => (A k l).2
  -- the coefficient form of the system
  have hrec : ∀ (k : Fin g) (Nn : ℕ),
      (hbase + (Nn : ℂ)) * z k Nn
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
    intro k Nn
    have hco : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hsys k]
    have hL : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = (hbase + (Nn : ℂ)) * z k Nn := rfl
    have hR : ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      change psSMul ((A k l : ↥SubexpPS) : PowerSeries ℂ)
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ)) = _
      rw [psSMul_apply_coset _ (y l).2 Nn]
    rw [← hL, hco, hR]
  have hzSub : ∀ k, Subexponential (fun n => ‖z k n‖) :=
    subexponential_of_system z a haSub hrec
  -- transport to an arbitrary block value
  obtain ⟨c, hc⟩ := hgen v
  have hcoeff : ∀ n : ℕ, S v (hbase + (n : ℂ))
      = ∑ l, qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
          ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ)) := by
    intro n
    have hcv : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, c l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hc]
    have hlhs : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        (hbase + (n : ℂ)) = S v (hbase + (n : ℂ)) := rfl
    rw [← hlhs, hcv, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => rfl)
  have hterm : ∀ l : Fin g, Subexponential (fun n : ℕ =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖) :=
    fun l => subexponential_qConv (c l).2 (QSeriesAt.support_neg (y l).2) (hzSub l)
  refine Subexponential.of_le (fun n => ?_)
    (Subexponential.finsetSum Finset.univ (fun l n =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖)
      (fun l _ => hterm l))
  rw [hcoeff n]
  exact norm_sum_le _ _

end DifferentialSpan

variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Support of the trace on the actual conformal-weight progression. -/
theorem trace_mem_QSeriesAt (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) :
    trace Y w ∈ QSeriesAt (h - W.centralCharge / 24) := by
  intro e he
  refine gradedTraceOp_eq_zero_of_weight_bot N (zeroMode A Y.val w) e ?_
  by_contra hbot
  obtain ⟨n, hn⟩ := hcw.2 _ hbot
  exact he n (by linear_combination hn)

/-- Remaining algebraic finiteness obligation (C₂ reduction of the insertion module).
Source: Miyamoto §§3–4; Huang §3. -/
def TraceSpanFinite (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) : Prop :=
  (blockSpanS (trace_mem_QSeriesAt Y hcw)).FG

/-- Remaining differential obligation (the intertwiner version of the omega recursion).
Source: Miyamoto §3; Huang §2. -/
def TraceDerivativeClosed (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) : Prop :=
  ∀ z ∈ blockSpanS (trace_mem_QSeriesAt Y hcw),
    qD (h - W.centralCharge / 24) z ∈ blockSpanS (trace_mem_QSeriesAt Y hcw)

/-- Coefficient growth for all insertion vectors. -/
def TraceSubexponential (Y : IntertwiningOperator A N N) (h : ℂ) : Prop :=
  ∀ w, Subexponential (fun n : ℕ => ‖trace Y w (h - W.centralCharge / 24 + n)‖)

/-- The two algebraic obligations imply subexponential growth. -/
theorem traceSubexponential_of_fg_closed (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (hfg : TraceSpanFinite Y hcw)
    (hclosed : TraceDerivativeClosed Y hcw) : TraceSubexponential Y h :=
  subexponential_of_fg_closed (trace_mem_QSeriesAt Y hcw) hfg hclosed

/-- Absolute convergence on the full open unit disc, conditional only on the two obligations. -/
theorem summable_trace_of_fg_closed (Y : IntertwiningOperator A N N) {h q : ℂ}
    (hcw : HasConformalWeight N h) (hfg : TraceSpanFinite Y hcw)
    (hclosed : TraceDerivativeClosed Y hcw) (hq : ‖q‖ < 1) (w : M₁) :
    Summable (fun n : ℕ => ‖trace Y w (h - W.centralCharge / 24 + n) * q ^ n‖) := by
  have hs := summable_of_subexponential (fun n : ℕ => norm_nonneg
    (trace Y w (h - W.centralCharge / 24 + n)))
    (traceSubexponential_of_fg_closed Y hcw hfg hclosed w) (norm_nonneg q) hq
  simpa only [norm_mul, norm_pow] using hs

/-- The analytic one-point value, with the conformal prefactor specified on the upper half-plane.
Use the HasSum theorem below to certify this total definition as a convergent trace. -/
noncomputable def traceFunction (Y : IntertwiningOperator A N N) (h : ℂ)
    (w : M₁) (τ : UpperHalfPlane) : ℂ :=
  qEvalAt (trace Y w) (h - W.centralCharge / 24) τ

/-- Certified evaluation of the full trace, including the factor q^(h-c/24). -/
theorem hasSum_trace_of_fg_closed (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (hfg : TraceSpanFinite Y hcw)
    (hclosed : TraceDerivativeClosed Y hcw) (w : M₁) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h - W.centralCharge / 24)) *
        (trace Y w (h - W.centralCharge / 24 + n) * qParam τ ^ n))
      (traceFunction Y h w τ) :=
  ((summable_trace_of_fg_closed Y hcw hfg hclosed
    (norm_qParam_lt_one τ) w).of_norm.hasSum).mul_left _

/-- Exact linear-map bridge to Zhu's existing formal blocks. -/
theorem trace_moduleIntertwinerHom (N : OrdVModule W M) :
    trace (moduleIntertwiner N) = torusOnePointHom N := by
  ext v e
  exact congrFun (trace_moduleIntertwiner N v) e

/-- Both residuals hold in the vertex-operator sector, with C₂-cofiniteness alone. -/
theorem trace_inputs_moduleIntertwiner (N : OrdVModule W M) {h : ℂ}
    (hcw : HasConformalWeight N h) (hC2 : C2Cofinite W) :
    TraceSpanFinite (moduleIntertwiner N) hcw ∧
      TraceDerivativeClosed (moduleIntertwiner N) hcw := by
  have hblock : IsFormalBlock W (trace (moduleIntertwiner N)) := by
    rw [trace_moduleIntertwinerHom]
    exact torusOnePointHom_isFormalBlock N
  exact ⟨fg_blockSpanS W (trace_mem_QSeriesAt _ hcw) hblock (vacuumGradeZero_holds W) hC2,
    fun _ hz => qD_mem_blockSpanS W (trace_mem_QSeriesAt _ hcw) hblock hz⟩

/-- Unconditional C₂ convergence for the vertex-operator specialization of the new trace. -/
theorem summable_trace_moduleIntertwiner (N : OrdVModule W M) {h q : ℂ}
    (hcw : HasConformalWeight N h) (hC2 : C2Cofinite W) (hq : ‖q‖ < 1) (v : V) :
    Summable (fun n : ℕ =>
      ‖trace (moduleIntertwiner N) v (h - W.centralCharge / 24 + n) * q ^ n‖) := by
  obtain ⟨hfg, hclosed⟩ := trace_inputs_moduleIntertwiner N hcw hC2
  exact summable_trace_of_fg_closed _ hcw hfg hclosed hq v

end VOA.Huang.GenusOne
