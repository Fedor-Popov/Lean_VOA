import VOA.Huang.GenusOneSlash

/-!
# The remaining two obligations for one-point S-closure

`InsertionSBlockCovariance` is the geometric block statement (Miyamoto,
math/0010180, Theorem 5.1). It does not mention intertwiners or trace realization.
`InsertionTraceSpanning` is the realization statement (ibid., Theorem 4.15,
using Theorem 2.10 and Lemmas 4.10–4.14). It does not mention S.

Both are true targets for an irreducible insertion over a strongly rational VOA
and a complete family of irreducible traced modules, with their conformal weights.
Neither is asserted here without a proof. The implication to the requested
S-transformation is proved with coefficients uniform in the insertion vector.
The principal-power convention differs from Miyamoto's normalized S by a constant
on one conformal-weight coset; no SL₂(ℤ) representation law is asserted.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators MatrixGroups
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Geometric residual: the homogeneous S-slash extends to a single analytic
insertion block, simultaneously on all square-weight spaces. The missing module
coordinate identities are distinct from scalar holomorphy and Serre covariance,
which are proved in `GenusOneSlash`. -/
def InsertionSBlockCovariance (A : OrdVModule W M₁) : Prop :=
  ∀ F : M₁ → ℂ → ℂ, IsInsertionAnalyticBlock A F →
    ∃ G : M₁ → ℂ → ℂ, IsInsertionAnalyticBlock A G ∧
      ∀ (α : ℂ) (w : M₁), sqL A 0 w = α • w → ∀ z ∈ imGT 0,
        G w z = sSlash α (F w) z

variable {ι : Type u} [Fintype ι]

/-- Realization residual: every full analytic insertion block is a sum of
intertwiner traces on the specified family. Intended hypotheses: strong rationality,
irreducible insertion, and a complete irreducible family with the specified weights.
This concerns all block relations, not all solutions of an arbitrary scalar MLDE. -/
def InsertionTraceSpanning (A : OrdVModule W M₁) (Mfam : ι → IrrModule W)
    (h : ι → ℂ) : Prop :=
  ∀ F : M₁ → ℂ → ℂ, IsInsertionAnalyticBlock A F →
    ∃ Z : ∀ j, IntertwiningOperator A (Mfam j).isMod (Mfam j).isMod,
      ∀ (w : M₁) (τ : UpperHalfPlane), F w (τ : ℂ) =
        ∑ j, traceFunction (Z j) (h j) w τ

/-- The desired S-law. One family of intertwiners works for every square-homogeneous
insertion vector and every point of the upper half-plane. -/
def InsertionSClosure (A : OrdVModule W M₁) (Mfam : ι → IrrModule W) (h : ι → ℂ) : Prop :=
  ∀ (i : ι) (Y : IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod),
    ∃ Z : ∀ j, IntertwiningOperator A (Mfam j).isMod (Mfam j).isMod,
      ∀ (α : ℂ) (w : M₁), sqL A 0 w = α • w → ∀ τ : UpperHalfPlane,
        traceFunction Y (h i) w (ModularGroup.S • τ) =
          (τ : ℂ) ^ α * ∑ j, traceFunction (Z j) (h j) w τ

/-- The requested S-law follows from geometric block covariance and trace
realization; all convergence and analytic-block hypotheses are discharged. -/
theorem insertionSClosure_of_covariance_spanning (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hcov : InsertionSBlockCovariance A) (hspan : InsertionTraceSpanning A Mfam h) :
    InsertionSClosure A Mfam h := by
  intro i Y
  obtain ⟨G, hG, hslash⟩ := hcov _
    (isInsertionAnalyticBlock_trace_of_irreducible hC2 hA Y (hcw i))
  obtain ⟨Z, hZ⟩ := hspan G hG
  refine ⟨Z, fun α w hw τ => ?_⟩
  have hs := hslash α w hw (τ : ℂ) τ.im_pos
  rw [sSlash, anEval_of_mem _ _ _ (mobiusC_mem_imGT ModularGroup.S τ.im_pos),
    mobiusC_coe, qEvalC_coe, hZ w τ] at hs
  change (∑ j, traceFunction (Z j) (h j) w τ) =
    (τ : ℂ) ^ (-α) * traceFunction Y (h i) w (ModularGroup.S • τ) at hs
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [hs, Complex.cpow_neg, ← mul_assoc,
    mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hτ)), one_mul]

/-- The scalar S-transform is already holomorphic; the residual concerns its
simultaneous extension satisfying the module block relations. -/
theorem differentiableOn_sSlash_trace (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Y : IntertwiningOperator A N N) {h : ℂ} (hcw : HasConformalWeight N h)
    (α : ℂ) (w : M₁) :
    DifferentiableOn ℂ (sSlash α (traceFunctionC Y h w)) (imGT 0) :=
  differentiableOn_sSlash α (differentiableOn_traceFunctionC_of_irreducible hC2 hA Y hcw w)

end VOA.Huang.GenusOne
