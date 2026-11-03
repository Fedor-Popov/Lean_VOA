import VOA.Huang.FusionTop
import VOA.Modularity.GradedTrace

/-!
# One-point formal traces with an intertwiner insertion

The insertion module is arbitrary and the traced module is ordinary.  The zero mode is
extended linearly using the insertion module's weight decomposition.  Only that mode
contributes to a diagonal trace.  No convergence or modular invariance is assumed here.

References: FHL, §5.4 (intertwiners); Miyamoto, arXiv:math/0010180, §3
(intertwiner trace functions); Huang, arXiv:math/0303049, §2 (formal trace calculus).
The coordinate correction U(1) needed for Huang's modular action is not included here.
-/

namespace VOA.Huang.GenusOne

open VOA Module
open scoped BigOperators

universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

/-- The zero-weight component: on weight `α`, take mode `α - 1`. -/
noncomputable def zeroMode (A : OrdVModule W M₁) (Y : IntertwiningModes M₁ M M) :
    M₁ →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  (DFinsupp.lsum ℂ (fun α => (Y (α - 1)).comp (A.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv A.weight).toLinearMap

theorem zeroMode_of_mem (A : OrdVModule W M₁) (Y : IntertwiningModes M₁ M M)
    {α : ℂ} {w : M₁} (hw : w ∈ A.weight α) : zeroMode A Y w = Y (α - 1) w := by
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  change (DFinsupp.lsum ℂ (fun α => (Y (α - 1)).comp (A.weight α).subtype))
    (DirectSum.decompose A.weight w) = _
  rw [DirectSum.decompose_of_mem A.weight hw]
  exact DFinsupp.lsum_single ℂ (fun α => (Y (α - 1)).comp (A.weight α).subtype)
    α ⟨w, hw⟩

theorem zeroMode_add (A : OrdVModule W M₁) (Y Z : IntertwiningModes M₁ M M) :
    zeroMode A (Y + Z) = zeroMode A Y + zeroMode A Z := by
  refine LinearMap.ext fun w => FusionTop.induction_weight A w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, LinearMap.add_apply]
  · intro α x hx
    rw [LinearMap.add_apply, zeroMode_of_mem _ _ hx, zeroMode_of_mem _ _ hx,
      zeroMode_of_mem _ _ hx]
    rfl

theorem zeroMode_smul (A : OrdVModule W M₁) (c : ℂ) (Y : IntertwiningModes M₁ M M) :
    zeroMode A (c • Y) = c • zeroMode A Y := by
  refine LinearMap.ext fun w => FusionTop.induction_weight A w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, LinearMap.smul_apply]
  · intro α x hx
    rw [LinearMap.smul_apply, zeroMode_of_mem _ _ hx, zeroMode_of_mem _ _ hx]
    rfl

variable {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- The weight shift of an arbitrary homogeneous intertwiner mode. -/
theorem weightShift_mode (Y : IntertwiningOperator A N N) {α : ℂ} {w : M₁}
    (hw : w ∈ A.weight α) (n : ℂ) : WeightShift N (Y.val n w) (α - n - 1) := by
  intro β x hx
  have h := FusionTop.mem_weight Y.property hw hx n
  rwa [show α + β - n - 1 = β + (α - n - 1) by ring] at h

/-- The zero mode really restricts to an endomorphism of every finite weight space. -/
theorem zeroMode_mem_weight (Y : IntertwiningOperator A N N) (w : M₁)
    {β : ℂ} {x : M} (hx : x ∈ N.weight β) : zeroMode A Y.val w x ∈ N.weight β := by
  refine FusionTop.induction_weight A w (by simp) (fun a b ha hb => ?_) ?_
  · rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  · intro α a ha
    rw [zeroMode_of_mem _ _ ha]
    have h := FusionTop.mem_weight Y.property ha hx (α - 1)
    rwa [show α + β - (α - 1) - 1 = β by ring] at h

/-- The restriction of `o_Y(w)` to the weight space of weight `β`. -/
noncomputable def zeroModeBlock (Y : IntertwiningOperator A N N) (w : M₁) (β : ℂ) :
    End ℂ (N.weight β) :=
  (zeroMode A Y.val w).restrict (fun _ hx => zeroMode_mem_weight Y w hx)

theorem zeroModeBlock_eq_weightBlock (Y : IntertwiningOperator A N N) (w : M₁) (β : ℂ) :
    zeroModeBlock Y w β = weightBlock N (zeroMode A Y.val w) β := by
  ext x
  exact (congrArg Subtype.val (internalProjTo_coe N.isInternal β
    ⟨zeroMode A Y.val w x, zeroMode_mem_weight Y w x.property⟩)).symm

/-- Formal `Tr_N o_Y(w) q^(L(0)-c/24)`, linear in the insertion vector. -/
noncomputable def trace (Y : IntertwiningOperator A N N) : M₁ →ₗ[ℂ] FormalQSeries where
  toFun w := gradedTraceOp N (zeroMode A Y.val w)
  map_add' w v := by rw [map_add, gradedTraceOp_add]
  map_smul' c w := by simp only [map_smul, gradedTraceOp_smul, RingHom.id_apply]

/-- Coefficients are actual finite-dimensional traces of restrictions, not just projections. -/
theorem trace_eq (Y : IntertwiningOperator A N N) (w : M₁) (e : ℂ) :
    trace Y w e =
      LinearMap.trace ℂ _ (zeroModeBlock Y w (e + W.centralCharge / 24)) := by
  rw [zeroModeBlock_eq_weightBlock]
  rfl

/-- Every nonzero-weight mode has zero diagonal trace. -/
theorem trace_mode_eq_zero (Y : IntertwiningOperator A N N) {α n : ℂ} {w : M₁}
    (hw : w ∈ A.weight α) (hn : n ≠ α - 1) (e : ℂ) :
    gradedTraceOp N (Y.val n w) e = 0 :=
  gradedTraceOp_eq_zero_of_shift N _ (by contrapose! hn; linear_combination -hn)
    (weightShift_mode Y hw n) e

/-- The coefficient of the cylinder trace of `Y(exp(t L(0)) w, exp t)`.
Here `t = 2πiz`; the exponent is written on the universal cover. -/
noncomputable def cylinderTraceCoeff (Y : IntertwiningOperator A N N)
    (α : ℂ) (w : M₁) (t e : ℂ) : ℂ :=
  ∑ᶠ n : ℂ, Complex.exp (t * (α - n - 1)) * gradedTraceOp N (Y.val n w) e

/-- The cylinder one-point trace is independent of the insertion coordinate, coefficientwise.
The sum over complex modes has at most one nonzero term. -/
theorem cylinderTraceCoeff_eq (Y : IntertwiningOperator A N N) {α : ℂ} {w : M₁}
    (hw : w ∈ A.weight α) (t e : ℂ) : cylinderTraceCoeff Y α w t e = trace Y w e := by
  unfold cylinderTraceCoeff
  rw [finsum_eq_single _ (α - 1) (fun n hn => by
    rw [trace_mode_eq_zero Y hw hn, mul_zero])]
  rw [show α - (α - 1) - 1 = 0 by ring, mul_zero, Complex.exp_zero, one_mul]
  change _ = gradedTraceOp N (zeroMode A Y.val w) e
  rw [zeroMode_of_mem _ _ hw]

/-- Linearity in the intertwining operator as well as in the insertion vector. -/
noncomputable def traceLinear :
    IntertwiningOperator A N N →ₗ[ℂ] (M₁ →ₗ[ℂ] FormalQSeries) where
  toFun := trace
  map_add' Y Z := by
    ext w e
    change gradedTraceOp N (zeroMode A (Y.val + Z.val) w) e = _
    rw [zeroMode_add, LinearMap.add_apply, gradedTraceOp_add]
    rfl
  map_smul' c Y := by
    ext w e
    change gradedTraceOp N (zeroMode A (c • Y.val) w) e = _
    rw [zeroMode_smul, LinearMap.smul_apply, gradedTraceOp_smul]
    rfl

/-- The formal trace has a lower bound on its support. -/
theorem trace_boundedBelow (Y : IntertwiningOperator A N N) (w : M₁) :
    ∃ B : ℝ, ∀ e : ℂ, (e + W.centralCharge / 24).re < B → trace Y w e = 0 :=
  gradedTraceOp_eq_zero_of_re_lt N _

/-- Compatibility with the library's vertex-operator zero mode. -/
theorem zeroMode_moduleIntertwiner (N : OrdVModule W M) :
    zeroMode (adjointModule W) (moduleIntertwiner N).val = oMod N := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction W.grading (motive := fun v =>
    zeroMode (adjointModule W) (moduleIntertwiner N).val v = oMod N v) hv ?_
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb])
  intro k a ha
  have ha' : a ∈ (adjointModule W).weight (k : ℂ) := by
    change a ∈ adjWeight W (k : ℂ)
    simpa only [adjWeight_cast] using ha
  rw [zeroMode_of_mem _ _ ha', oMod_of_mem_grading N ha]
  change moduleModes N ((k : ℂ) - 1) a = _
  rw [show (k : ℂ) - 1 = ((k - 1 : ℤ) : ℂ) by push_cast; ring,
    moduleModes_intCast]
  rfl

/-- The vacuum insertion sector agrees exactly with Zhu's one-point series. -/
theorem trace_moduleIntertwiner (N : OrdVModule W M) (v : V) :
    trace (moduleIntertwiner N) v = onePoint N v := by
  change gradedTraceOp N (zeroMode (adjointModule W) (moduleIntertwiner N).val v) = _
  rw [zeroMode_moduleIntertwiner, gradedTraceOp_oMod]

end VOA.Huang.GenusOne
