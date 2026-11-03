import VOA.Huang.GenusTwoPointTrace
import VOA.Huang.GenusOneQEquationAlgebra
import VOA.Huang.HuangODEModes

/-!
# Two-insertion trace commutators

The two insertion terms in the Ward identity are derived from the actual FHL
commutators. All sums have a cutoff depending only on the insertion vectors.
Nonzero weight shifts give a recurrence between different traced weights, not
vanishing of a commutator at each weight. These are raw plane-coordinate
identities; geometric modification and collection into elliptic kernels remain
separate obligations.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Module
open scoped BigOperators
universe u
variable {V E₁ E₂ M K : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W E₁} {A₂ : OrdVModule W E₂}
  {N : OrdVModule W M} {Q : OrdVModule W K}

/-- Commuting a vertex mode through two rectangular intertwiner modes. -/
theorem product_commutator (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) (a : V) (w₁ : E₁) (w₂ : E₂)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) :
    mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) -
      ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) * mode (N.YM a) i =
      (∑ p ∈ Finset.range J, cbz i p •
        ((Y₁.val (i + n₁ - p) (mode (A₁.YM a) p w₁)).comp (Y₂.val n₂ w₂))) +
      ∑ p ∈ Finset.range J, cbz i p •
        ((Y₁.val n₁ w₁).comp (Y₂.val (i + n₂ - p) (mode (A₂.YM a) p w₂))) := by
  ext x
  have h₂ := HuangODEModes.comm_range Y₂.property a w₂ x i n₂ J
    (fun p hp => (hJ p hp).2)
  have h₁ := HuangODEModes.comm_range Y₁.property a w₁ (Y₂.val n₂ w₂ x) i n₁ J
    (fun p hp => (hJ p hp).1)
  change mode (N.YM a) i (Y₁.val n₁ w₁ (Y₂.val n₂ w₂ x)) -
    Y₁.val n₁ w₁ (Y₂.val n₂ w₂ (mode (N.YM a) i x)) = _
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rw [h₂, map_sub, map_sum]
  simp only [map_smul]
  rw [h₁]
  abel

/-- The insertion part of the uncollected Ward relation at one q-degree. -/
noncomputable def wardTrace (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) (a : V) (w₁ : E₁) (w₂ : E₂)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) (e : ℂ) : ℂ :=
  (∑ p ∈ Finset.range J, cbz i p *
    productModeTrace Y₁ Y₂ (mode (A₁.YM a) p w₁) w₂ (i + n₁ - p) n₂ e) +
  ∑ p ∈ Finset.range J, cbz i p *
    productModeTrace Y₁ Y₂ w₁ (mode (A₂.YM a) p w₂) n₁ (i + n₂ - p) e

theorem trace_product_commutator (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) (a : V) (w₁ : E₁) (w₂ : E₂)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) -
      ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) * mode (N.YM a) i) e =
      wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J e := by
  rw [product_commutator Y₁ Y₂ a w₁ w₂ i n₁ n₂ J hJ, ← gradedTraceAt_apply]
  simp only [map_add, map_sum, map_smul, gradedTraceAt_apply, smul_eq_mul,
    wardTrace, productModeTrace]

/-- Total weight shift of the actual composite, with no trace assumption. -/
theorem weightShift_product (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (n₁ n₂ : ℂ) :
    WeightShift N ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))
      (α₁ + α₂ - n₁ - n₂ - 2) := by
  intro β x hx
  have h := FusionTop.mem_weight Y₁.property h₁
    (FusionTop.mem_weight Y₂.property h₂ hx n₂) n₁
  convert h using 1
  congr 1
  ring

/-- The two-insertion coefficient recurrence. Its shift is essential. -/
theorem trace_product_step (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {k : ℤ} {α₁ α₂ : ℂ}
    {a : V} {w₁ : E₁} {w₂ : E₂} (ha : a ∈ W.grading k)
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (i : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)))
        (e + ((k : ℂ) - i - 1)) =
      gradedTraceOp N (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) e -
        wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J e := by
  have hshift := weightShift_product Y₁ Y₂ h₁ h₂ n₁ n₂
  rw [show α₁ + α₂ - n₁ - n₂ - 2 = -((k : ℂ) - i - 1) by
    linear_combination -hn] at hshift
  have h := gradedTraceOp_comm_shift N _ _ _ hshift (VOA.weightShift_mode N ha i) e
  have hc := trace_product_commutator Y₁ Y₂ a w₁ w₂ i n₁ n₂ J hJ e
  rw [gradedTraceOp_sub, Pi.sub_apply, h] at hc
  linear_combination -hc

/-- Simultaneous zero-shift Ward identity; both insertion terms are needed. -/
theorem wardTrace_zero_shift (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {k : ℤ} {α₁ α₂ : ℂ}
    {a : V} {w₁ : E₁} {w₂ : E₂} (ha : a ∈ W.grading k)
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (n₁ n₂ : ℂ) (hn : n₁ + n₂ = α₁ + α₂ - 2) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) (e : ℂ) :
    wardTrace Y₁ Y₂ a w₁ w₂ (k - 1) n₁ n₂ J e = 0 := by
  have h := trace_product_step Y₁ Y₂ ha h₁ h₂ (k - 1) n₁ n₂
    (by push_cast; linear_combination hn) J hJ e
  rw [show (k : ℂ) - ((k - 1 : ℤ) : ℂ) - 1 = 0 by push_cast; ring, add_zero] at h
  linear_combination h

/-- Positive shifts are inverted by a finite downward telescope. -/
theorem trace_product_geom_of_lt (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {k : ℤ} {α₁ α₂ : ℂ}
    {a : V} {w₁ : E₁} {w₂ : E₂} (ha : a ∈ W.grading k)
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    {i : ℤ} (hi : i < k - 1) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) (e : ℂ) :
    ∃ L : ℕ, gradedTraceOp N
      (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) e =
      - ∑ j ∈ Finset.range L, wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J
        (e - ((j : ℂ) + 1) * ((k : ℂ) - i - 1)) := by
  have hs : 0 < ((k : ℂ) - i - 1).re := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    exact_mod_cast (show 0 < k - i - 1 by omega)
  obtain ⟨L, hL⟩ := exists_gradedTraceOp_vanish N
    (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) hs e
  refine ⟨L, ?_⟩
  have h := gradedTrace_geomSolve _ (fun e => -wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J e) _
    (fun e => by simpa only [sub_eq_add_neg] using
      trace_product_step Y₁ Y₂ ha h₁ h₂ i n₁ n₂ hn J hJ e) e L hL
  simpa only [Finset.sum_neg_distrib] using h

/-- Negative shifts are inverted by the upward telescope. -/
theorem trace_product_geom_of_gt (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) {k : ℤ} {α₁ α₂ : ℂ}
    {a : V} {w₁ : E₁} {w₂ : E₂} (ha : a ∈ W.grading k)
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    {i : ℤ} (hi : k - 1 < i) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : QEquation.TailBound A₁.toWeakModule A₂.toWeakModule a w₁ w₂ J) (e : ℂ) :
    ∃ L : ℕ, gradedTraceOp N
      (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) e =
      ∑ j ∈ Finset.range L, wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J
        (e + (j : ℂ) * ((k : ℂ) - i - 1)) := by
  have hs : ((k : ℂ) - i - 1).re < 0 := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    exact_mod_cast (show k - i - 1 < 0 by omega)
  obtain ⟨L, hL⟩ := exists_gradedTraceOp_vanish_up N
    (mode (N.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) hs e
  refine ⟨L, ?_⟩
  have h := gradedTrace_geomSolve_up _ (fun e => -wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J e) _
    (fun e => by simpa only [sub_eq_add_neg] using
      trace_product_step Y₁ Y₂ ha h₁ h₂ i n₁ n₂ hn J hJ e) e L hL
  simpa only [Finset.sum_neg_distrib, neg_neg] using h

/-- Actual energy insertion; it is not yet expressed by insertion descendants. -/
noncomputable def traceEnergy (N : OrdVModule W M) : Module.End ℂ M :=
  mode (N.YM W.conformalVector) 1 - (W.centralCharge / 24) • 1

theorem gradedTraceOp_traceEnergy (T : Module.End ℂ M) :
    gradedTraceOp N (traceEnergy N * T) = qDeriv (gradedTraceOp N T) := by
  funext e
  rw [traceEnergy, sub_mul, smul_mul_assoc, one_mul, gradedTraceOp_sub,
    Pi.sub_apply, gradedTraceOp_smul, Pi.smul_apply, gradedTraceOp_L0_mul]
  simp only [qDeriv, smul_eq_mul]
  ring

/-- All formal q-derivatives of the actual two-mode trace are energy moments.
This does not assert a differential Ward law in the two-insertion quotient. -/
theorem productTrace_energy_moments (Y₁ : IntertwiningOperator A₁ Q N)
    (Y₂ : IntertwiningOperator A₂ N Q) (w₁ : E₁) (w₂ : E₂) (n₁ n₂ : ℂ) (j : ℕ) :
    gradedTraceOp N ((traceEnergy N) ^ j * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) =
      QEquation.qIterate (fun _ => qDeriv) (productModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂) j := by
  induction j with
  | zero => simp only [pow_zero, one_mul, QEquation.qIterate]; rfl
  | succ j ih =>
    rw [pow_succ', mul_assoc, gradedTraceOp_traceEnergy, ih, QEquation.qIterate]

end VOA.Huang.GenusTwoPoint
