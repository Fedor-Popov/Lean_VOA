import VOA.Huang.GenusOneConvergence
import VOA.Modularity.GNProp8Closure

/-!
# The T-law and the vertex-operator boundary of genus-one modularity

The T-law uses only the conformal-weight progression.  In the vertex-operator sector,
the new trace functions satisfy precisely the pinned Zhu transformation law, with the
same representation and the same square-weight convention.  General intertwiner
S-invariance is not asserted: it needs module square coordinates and trace spanning.

Sources: Miyamoto, arXiv:math/0010180, §§3–5; Zhu, JAMS 9 (1996), §5.
-/

namespace VOA.Huang.GenusOne

open VOA VHat VHat.DLM3 Module
open scoped BigOperators MatrixGroups

universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Formal T-periodicity for every intertwiner insertion. -/
theorem trace_T_transform (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) :
    qShift (trace Y w) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)) • trace Y w := by
  funext e
  simp only [qShift, Pi.smul_apply, smul_eq_mul]
  by_cases he : ∃ n : ℕ, e = h - W.centralCharge / 24 + n
  · obtain ⟨n, rfl⟩ := he
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24 + n)
        = 2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)
          + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · rw [trace_mem_QSeriesAt Y hcw w e (by simpa only [not_exists] using he), mul_zero, mul_zero]

/-- T-transformation of the defined trace value. Convergence is certified separately by
`hasSum_trace_of_fg_closed`; this identity itself is termwise. -/
theorem traceFunction_translate (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (w : M₁) {τ τ' : UpperHalfPlane}
    (hτ : (τ' : ℂ) = (τ : ℂ) + 1) :
    traceFunction Y h w τ' =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)) *
        traceFunction Y h w τ := by
  unfold traceFunction
  rw [qEvalAt_translate _ _ hτ, trace_T_transform Y hcw w, qEvalAt_smul]

section VertexSector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The module vertex-operator traces, evaluated by the new definitions, satisfy Zhu's
square-weight law with the specified modular representation. -/
def ModuleTraceModularity (D : ModularData W ι) : Prop :=
  ∀ (γ : SL(2, ℤ)) (n : ℕ) (v : V), v ∈ sqWeightSpace W (n : ℂ) →
    ∀ (i : ι) (τ : UpperHalfPlane),
      traceFunction (moduleIntertwiner (D.Mfam i).isMod) (D.h i) v (γ • τ)
        = autFactor γ τ ^ n * ∑ j, D.rep γ i j *
          traceFunction (moduleIntertwiner (D.Mfam j).isMod) (D.h j) v τ

/-- Exact agreement with the existing theorem, without changing its weight convention. -/
theorem moduleTraceModularity_iff (D : ModularData W ι) :
    ModuleTraceModularity D ↔ ZhuModularityAnalytic D := by
  simp only [ModuleTraceModularity, ZhuModularityAnalytic, traceFunction,
    trace_moduleIntertwiner, traceFun, torusOnePoint]

/-- Pinned Zhu modularity transported to the intertwiner-trace definition. The regular-bottom
projection remains explicit, just as in the source theorem; the PBW theorem `VOA.pbw` is not used.
-/
theorem moduleTraceModularity_pinned_of_C2Cofinite [Finite (Φ W)]
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ModuleTraceModularity D := by
  obtain ⟨D, hM, hh, hD⟩ :=
    zhuModularity_pinned_of_C2Cofinite Mfam h hC2 hss Pr hcard hcw hsep
  exact ⟨D, hM, hh, (moduleTraceModularity_iff D).mpr hD⟩

end VertexSector
end VOA.Huang.GenusOne
