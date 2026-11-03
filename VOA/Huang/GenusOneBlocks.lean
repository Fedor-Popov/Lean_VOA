import VOA.Huang.GenusOneHolomorphic

/-!
# Genus-one blocks with module insertions

The three relations are the module version of Zhu's block conditions, with the
actual square modes. Formal trace blocks satisfy them unconditionally; convergence
transports them to holomorphic blocks. Source: Miyamoto, math/0010180, Definition
4.2, Proposition 4.3 and Theorem 4.7. Trace spanning (Theorem 4.15) is a separate obligation.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Formal insertion blocks; no support or growth is built into the relations. -/
structure IsInsertionFormalBlock (A : OrdVModule W M₁)
    (S : M₁ →ₗ[ℂ] FormalQSeries) : Prop where
  vanish : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ W.grading (k : ℤ), ∀ w,
    S (sqAct A a k 0 w) = 0
  negTwo : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ W.grading (k : ℤ), ∀ w,
    S (sqAct A a k (-2) w) + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ) •
      qConv (zhuG (m + 1)) (S (sqAct A a k (2 * (m + 1) - 2 : ℤ) w)) = 0
  omega : ∀ w, S (sqL A (-2) w) = qDeriv (S w) +
    ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) w))

/-- Every intertwiner trace satisfies all three formal block relations. -/
theorem isInsertionFormalBlock_trace (Y : IntertwiningOperator A N N) :
    IsInsertionFormalBlock A (trace Y) :=
  ⟨fun _ hk _ ha w => trace_sqAct_zero Y ha hk w,
    fun _ hk _ ha w => trace_sqAct_negTwo Y hk ha w, trace_sqL_negTwo Y⟩

theorem sqAct_tail_eventually_zero (A : OrdVModule W M₁) (a : V) (k : ℕ) (w : M₁) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → sqAct A a k (2 * (m + 1) - 2 : ℤ) w = 0 := by
  obtain ⟨K, hK⟩ := sqAct_eventually_zero A a k w
  exact ⟨K.toNat, fun m hm => hK _ (by omega)⟩

theorem sqL_tail_eventually_zero (A : OrdVModule W M₁) (w : M₁) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → sqL A (2 * (m + 1) - 2 : ℤ) w = 0 := by
  obtain ⟨K, hK⟩ := sqAct_eventually_zero A W.conformalVector 2 w
  refine ⟨K.toNat, fun m hm => ?_⟩
  simp only [sqL, show (2 * (m + 1) - 2 : ℤ) ≠ -2 by omega,
    if_false, zero_smul, sub_zero]
  exact hK _ (by omega)

structure IsInsertionAnalyticBlock (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ) : Prop where
  /-- Each `F v` is holomorphic on the upper half-plane. -/
  holo : ∀ v : M₁, DifferentiableOn ℂ (F v) (imGT 0)
  /-- Linearity in `v`. -/
  addv : ∀ (v w : M₁) (z : ℂ), F (v + w) z = F v z + F w z
  /-- Homogeneity in `v`. -/
  smulv : ∀ (c : ℂ) (v : M₁) (z : ℂ), F (c • v) z = c * F v z
  /-- (i) `F(a[0]v) = 0`. -/
  vanish : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : M₁, F (sqAct A a ka 0 v) = 0
  /-- (ii) Zhu's `[−2]`-identity. -/
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ (v : M₁), ∀ z ∈ imGT 0,
    F (sqAct A a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) = 0
  /-- (iii) The `ω`-recursion — the seed of the modular differential equation. -/
  omega : ∀ (v : M₁), ∀ z ∈ imGT 0,
    F (sqL A (-2) v) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z


theorem isInsertionAnalyticBlock_of_formal (S : M₁ →ₗ[ℂ] FormalQSeries) (h : ℂ)
    (hsupp : ∀ (v : M₁) (i : ℤ), i < 0 → S v (h + (i : ℂ)) = 0)
    (hsub : ∀ v : M₁, Subexponential (fun n : ℕ => ‖S v (h + (n : ℂ))‖))
    (hS : IsInsertionFormalBlock A S) :
    IsInsertionAnalyticBlock A (anEval S h) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- holomorphy
    intro v z hz
    have hd : DifferentiableAt ℂ (qEvalC (S v) h) z := by
      have hz0 : (0 : ℝ) < z.im := hz
      have hc : 0 < z.im / 2 := by linarith
      have hzc : z ∈ imGT (z.im / 2) := by change z.im / 2 < z.im; linarith
      exact (hasDerivAt_qEvalC (S v) h (hsub v) hc hzc).differentiableAt
    exact ((hd.congr_of_eventuallyEq
      (anEval_eventuallyEq S h v hz)).differentiableWithinAt)
  · -- additivity
    intro v w z
    by_cases hz : z ∈ imGT 0
    · rw [anEval_of_mem _ _ _ hz, anEval_of_mem _ _ _ hz, anEval_of_mem _ _ _ hz, map_add,
        qEvalC_add _ _ _ (summable_qTerm (S v) h (hsub v) hz) (summable_qTerm (S w) h (hsub w) hz)]
    · rw [anEval, anEval, anEval, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
        Set.indicator_of_notMem hz, add_zero]
  · exact anEval_smul S h
  · -- (i)
    intro ka hka a ha v
    funext z
    rw [anEval, hS.vanish ka hka a ha v]
    by_cases hz : z ∈ imGT 0
    · rw [Set.indicator_of_mem hz, qEvalC_zero]; rfl
    · rw [Set.indicator_of_notMem hz]; rfl
  · -- (ii)
    intro ka hka a ha v z hz
    obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a ka v
    have hfin : (Function.support fun m : ℕ => ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v))).Finite := by
      refine Set.Finite.subset (Set.finite_Iio K) (fun m hm => ?_)
      simp only [Function.mem_support, ne_eq] at hm
      simp only [Set.mem_Iio]
      by_contra hc
      push Not at hc
      exact hm (by rw [hK m hc, map_zero, qConv_zero_right, smul_zero])
    have hlaw := hS.negTwo ka hka a ha v
    have hsum1 : Summable (fun n : ℕ => qTerm (S (sqAct A a ka (-2) v)) h n z) :=
      summable_qTerm _ h (hsub _) hz
    have hsum2 : ∀ m : ℕ, Summable (fun n : ℕ => qTerm (((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      intro m
      refine ((summable_qTerm_qConv_zhuG S h hsupp hsub (m + 1)
        (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) hz).mul_left
        (((2 * (m + 1) - 1 : ℕ) : ℂ))).congr (fun n => ?_)
      rw [qTerm, qTerm, Pi.smul_apply, smul_eq_mul]
      ring
    have hsumfin : Summable (fun n : ℕ => qTerm (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        • qConv (zhuG (m + 1)) (S (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      have hs : Function.support (fun m : ℕ => ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (S (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v)))
          ⊆ (hfin.toFinset : Set ℕ) := by intro m hm; simpa using hm
      rw [finsum_eq_finsetSum_of_support_subset _ hs]
      exact summable_qTerm_finset _ _ h z (fun m _ => hsum2 m)
    have hev := congrArg (fun χ : FormalQSeries => qEvalC χ h z) hlaw
    simp only at hev
    rw [qEvalC_add _ _ _ hsum1 hsumfin, qEvalC_zero,
      qEvalC_finsum _ h hfin hsum2] at hev
    rw [anEval_of_mem _ _ _ hz, ← hev]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [qEvalC_smul, qEvalC_qConv_zhuG S h hsupp hsub (m + 1)
      (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) hz, anEval_of_mem _ _ _ hz]
  · -- (iii)
    intro v z hz
    obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A v
    have hfin : (Function.support fun m : ℕ =>
        qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) v))).Finite := by
      refine Set.Finite.subset (Set.finite_Iio K) (fun m hm => ?_)
      simp only [Function.mem_support, ne_eq] at hm
      simp only [Set.mem_Iio]
      by_contra hc
      push Not at hc
      exact hm (by rw [hK m hc, map_zero, qConv_zero_right])
    have hlaw := hS.omega v
    have hsumD : Summable (fun n : ℕ => qTerm (qDeriv (S v)) h n z) :=
      summable_qTerm_qDeriv (S v) h (hsub v) hz
    have hsum2 : ∀ m : ℕ, Summable (fun n : ℕ =>
        qTerm (qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) v))) h n z) :=
      fun m => summable_qTerm_qConv_zhuG S h hsupp hsub (m + 1)
        (sqL A (2 * (m + 1) - 2 : ℤ) v) hz
    have hsumfin : Summable (fun n : ℕ => qTerm (∑ᶠ m : ℕ,
        qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) v))) h n z) := by
      have hs : Function.support (fun m : ℕ =>
          qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) v)))
          ⊆ (hfin.toFinset : Set ℕ) := by intro m hm; simpa using hm
      rw [finsum_eq_finsetSum_of_support_subset _ hs]
      exact summable_qTerm_finset _ _ h z (fun m _ => hsum2 m)
    have hev := congrArg (fun χ : FormalQSeries => qEvalC χ h z) hlaw
    simp only at hev
    rw [qEvalC_add _ _ _ hsumD hsumfin, qEvalC_qDeriv (S v) h (hsub v) hz,
      qEvalC_finsum _ h hfin hsum2] at hev
    rw [anEval_of_mem _ _ _ hz, hev, anEval_deriv S h v hz]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [qEvalC_qConv_zhuG S h hsupp hsub (m + 1) (sqL A (2 * (m + 1) - 2 : ℤ) v) hz,
      anEval_of_mem _ _ _ hz]

/-- Holomorphic block packaging for C₂-cofinite insertion modules. -/
theorem isInsertionAnalyticBlock_trace_of_moduleC2 (Y : IntertwiningOperator A N N)
    {h : ℂ} (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hcw : HasConformalWeight N h) :
    IsInsertionAnalyticBlock A (anEval (trace Y) (h - W.centralCharge / 24)) :=
  isInsertionAnalyticBlock_of_formal (trace Y) _
    (fun w => QSeriesAt.support_neg (trace_mem_QSeriesAt Y hcw w))
    (traceSubexponential_of_fg_closed Y hcw (traceSpanFinite_of_moduleC2 Y hAC2 hcw)
      (traceDerivativeClosed_holds Y hcw)) (isInsertionFormalBlock_trace Y)

/-- The full analytic block conditions, for arbitrary intertwiners with irreducible insertion. -/
theorem isInsertionAnalyticBlock_trace_of_irreducible (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) :
    IsInsertionAnalyticBlock A (anEval (trace Y) (h - W.centralCharge / 24)) :=
  isInsertionAnalyticBlock_trace_of_moduleC2 Y (moduleC2_of_irreducible hC2 hA) hcw

end VOA.Huang.GenusOne
