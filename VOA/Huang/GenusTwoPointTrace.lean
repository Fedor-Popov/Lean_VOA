import VOA.Huang.GenusOneTrace
import VOA.Huang.AssocTarget

/-!
# Raw two-intertwiner trace coefficients

These are unmodified plane-coordinate coefficients, before Huang's U(x) change.
The intermediate module may differ from the traced module. No infinite trace or
coordinate-mode sum is taken in this file. In particular no convergence is implicit.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Module MatrixCoeff
open scoped BigOperators
universe u
variable {V E₁ E₂ M K : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W E₁} {A₂ : OrdVModule W E₂}
  {N : OrdVModule W M} {Q : OrdVModule W K}

/-- Actual finite-dimensional diagonal trace of a pair of rectangular modes. -/
noncomputable def productModeTrace (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) (w₁ : E₁) (w₂ : E₂) (n₁ n₂ e : ℂ) : ℂ :=
  gradedTraceOp N ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) e

/-- A two-point trace is supported on the total weight-conservation line. -/
theorem productModeTrace_eq_zero (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    {n₁ n₂ : ℂ} (hn : n₁ + n₂ ≠ α₁ + α₂ - 2) (e : ℂ) :
    productModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ e = 0 := by
  apply gradedTraceOp_eq_zero_of_shift N _
    (s := α₁ + α₂ - n₁ - n₂ - 2)
  · contrapose! hn
    linear_combination -hn
  · intro β x hx
    have hm := FusionTop.mem_weight Y₁.property h₁
      (FusionTop.mem_weight Y₂.property h₂ hx n₂) n₁
    convert hm using 1
    congr 1
    ring

/-- A coordinate functional on a weight space, extended by its canonical projection. -/
noncomputable def weightFunctional {ι : Type*} (N : OrdVModule W M) (β : ℂ)
    (b : Basis ι ℂ (N.weight β)) (i : ι) : M →ₗ[ℂ] ℂ :=
  (b.coord i).comp (internalProjTo N.isInternal β)

theorem supportedAt_weightFunctional {ι : Type*} (N : OrdVModule W M) (β : ℂ)
    (b : Basis ι ℂ (N.weight β)) (i : ι) :
    SupportedAt N (weightFunctional N β b i) β := by
  intro α hα x hx
  simp only [weightFunctional, LinearMap.comp_apply,
    internalProjTo_eq_zero_of_ne N hx (Ne.symm hα), map_zero]

/-- The basis formula uses only finitely many matrix coefficients. -/
theorem productModeTrace_eq_sum {ι : Type*} [Fintype ι]
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    (w₁ : E₁) (w₂ : E₂) (n₁ n₂ β : ℂ) (b : Basis ι ℂ (N.weight β)) :
    productModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ (β - W.centralCharge / 24) =
      ∑ i, prodCoeff Y₁.val Y₂.val (weightFunctional N β b i)
        w₁ w₂ (b i) n₁ n₂ := by
  classical
  change (fun γ => LinearMap.trace ℂ (N.weight γ)
    (weightBlock N ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) γ))
    (β - W.centralCharge / 24 + W.centralCharge / 24) = _
  rw [show β - W.centralCharge / 24 + W.centralCharge / 24 = β by ring]
  dsimp only
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, weightFunctional,
    Basis.coord_apply, LinearMap.comp_apply, prodCoeff, weightBlock]
  rfl

/-- Trace of an iterate mode, before summing its intermediate weights. -/
noncomputable def iterateModeTrace (Y₃ : IntertwiningOperator Q N N)
    (Y₄ : IntertwiningOperator A₁ A₂ Q) (w₁ : E₁) (w₂ : E₂) (n₀ n₂ e : ℂ) : ℂ :=
  gradedTraceOp N (Y₃.val n₂ (Y₄.val n₀ w₁ w₂)) e

/-- Weight conservation identifies the outer iterate mode with the one-point zero mode. -/
theorem iterateModeTrace_eq_onePoint (Y₃ : IntertwiningOperator Q N N)
    (Y₄ : IntertwiningOperator A₁ A₂ Q) {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (n₀ e : ℂ) :
    iterateModeTrace Y₃ Y₄ w₁ w₂ n₀ (α₁ + α₂ - n₀ - 2) e =
      GenusOne.trace Y₃ (Y₄.val n₀ w₁ w₂) e := by
  change _ = gradedTraceOp N (GenusOne.zeroMode Q Y₃.val (Y₄.val n₀ w₁ w₂)) e
  rw [GenusOne.zeroMode_of_mem Q Y₃.val
    (FusionTop.mem_weight Y₄.property h₁ h₂ n₀)]
  change gradedTraceOp N (Y₃.val (α₁ + α₂ - n₀ - 2) _) e =
    gradedTraceOp N (Y₃.val (α₁ + α₂ - n₀ - 1 - 1) _) e
  rw [show α₁ + α₂ - n₀ - 2 = α₁ + α₂ - n₀ - 1 - 1 by ring]

theorem iterateModeTrace_eq_sum {ι : Type*} [Fintype ι]
    (Y₃ : IntertwiningOperator Q N N) (Y₄ : IntertwiningOperator A₁ A₂ Q)
    (w₁ : E₁) (w₂ : E₂) (n₀ n₂ β : ℂ) (b : Basis ι ℂ (N.weight β)) :
    iterateModeTrace Y₃ Y₄ w₁ w₂ n₀ n₂ (β - W.centralCharge / 24) =
      ∑ i, iterCoeff Y₃.val Y₄.val (weightFunctional N β b i)
        w₁ w₂ (b i) n₀ n₂ := by
  classical
  change (fun γ => LinearMap.trace ℂ (N.weight γ)
    (weightBlock N (Y₃.val n₂ (Y₄.val n₀ w₁ w₂)) γ))
    (β - W.centralCharge / 24 + W.centralCharge / 24) = _
  rw [show β - W.centralCharge / 24 + W.centralCharge / 24 = β by ring]
  dsimp only
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, weightFunctional,
    Basis.coord_apply, LinearMap.comp_apply, iterCoeff, weightBlock]
  rfl

end VOA.Huang.GenusTwoPoint
