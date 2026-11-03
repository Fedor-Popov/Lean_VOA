import VOA.Huang.GenusTwoPointSepCuspWardResidual

/-!
# Transport of the mode between the two intertwining operators

The two slot commutators are kept separate. Moving the middle mode to the
trace boundary gives different geometric factors for the two slots. These
identities use finite-dimensional graded traces and formal q-series only.
They do not assert the spatially collected cusp Ward identities.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module QEquation
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The first-slot commutator, before spatial evaluation. -/
def leftWardTraceSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  ∑ p ∈ Finset.range J, (cbz i p) • operatorTraceSeries N
    ((Y₁.val (i + n₁ - p) (mode (P₁.isMod.YM a) p x)).comp (Y₂.val n₂ y))

/-- The second-slot commutator, with the product order unchanged. -/
def rightWardTraceSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  ∑ p ∈ Finset.range J, (cbz i p) • operatorTraceSeries N
    ((Y₁.val n₁ x).comp (Y₂.val (i + n₂ - p) (mode (P₂.isMod.YM a) p y)))

theorem wardTraceSeries_eq_slots
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) :
    wardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J =
      leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J +
        rightWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J := by
  ext n
  simp [wardTraceSeries, wardTrace, leftWardTraceSeries, rightWardTraceSeries,
    productModeTrace]

/-- Jacobi in the first slot, on each finite-dimensional traced weight. -/
theorem trace_middle_eq_left_sub
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N ((Y₁.val n₁ x).comp
      ((mode (Q.isMod.YM a) i).comp (Y₂.val n₂ y))) =
      operatorTraceSeries N
        (mode (N.isMod.YM a) i * ((Y₁.val n₁ x).comp (Y₂.val n₂ y))) -
        leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J := by
  have he : mode (N.isMod.YM a) i * ((Y₁.val n₁ x).comp (Y₂.val n₂ y)) -
      (Y₁.val n₁ x).comp ((mode (Q.isMod.YM a) i).comp (Y₂.val n₂ y)) =
      ∑ p ∈ Finset.range J, cbz i p •
        (Y₁.val (i + n₁ - p) (mode (P₁.isMod.YM a) p x)).comp (Y₂.val n₂ y) := by
    ext v
    simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rw [HuangODEModes.comm_range Y₁.property a x (Y₂.val n₂ y v) i n₁ J
      (fun p hp => (hJ p hp).1)]
    abel
  ext n
  have ht := congrArg (fun T => gradedTraceAt N.isMod
    (N.h - W.centralCharge / 24 + n) T) he
  simp only [map_sub, map_sum, map_smul, gradedTraceAt_apply, smul_eq_mul] at ht
  simp only [map_sub, coeff_operatorTraceSeries, leftWardTraceSeries,
    map_sum, PowerSeries.coeff_smul, smul_eq_mul]
  linear_combination -ht

/-- The geometric denominator differs from its shifted version by one. -/
theorem geometricDenominator_sub_one {d : ℕ} (hd : 0 < d) :
    geometricDenominator d - 1 = PowerSeries.X ^ d * geometricDenominator d := by
  have h := geometricDenominator_mul hd
  linear_combination h

/-- A lowering middle mode: the first slot retains the q-shift. -/
theorem trace_middle_q_transport_neg
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k i : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) {d : ℕ} (hd : 0 < d)
    (hdi : i - k + 1 = (d : ℤ)) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N ((Y₁.val n₁ x).comp
      ((mode (Q.isMod.YM a) i).comp (Y₂.val n₂ y))) =
      PowerSeries.X ^ d * geometricDenominator d *
        leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J +
      geometricDenominator d * rightWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J := by
  rw [trace_middle_eq_left_sub Y₁ Y₂ a x y i n₁ n₂ J hJ,
    trace_product_q_transport_neg Y₁ Y₂ ha hx hy hd hdi n₁ n₂ hn J hJ,
    wardTraceSeries_eq_slots]
  linear_combination
    geometricDenominator_sub_one hd * leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J

/-- A raising middle mode: the second slot retains the q-shift. -/
theorem trace_middle_q_transport_pos
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k i : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) {d : ℕ} (hd : 0 < d)
    (hdi : k - i - 1 = (d : ℤ)) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N ((Y₁.val n₁ x).comp
      ((mode (Q.isMod.YM a) i).comp (Y₂.val n₂ y))) =
      -(geometricDenominator d * leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J) -
      PowerSeries.X ^ d * geometricDenominator d *
        rightWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J := by
  rw [trace_middle_eq_left_sub Y₁ Y₂ a x y i n₁ n₂ J hJ,
    trace_product_q_transport_pos Y₁ Y₂ ha hx hy hd hdi n₁ n₂ hn J hJ,
    wardTraceSeries_eq_slots]
  linear_combination
    geometricDenominator_sub_one hd * leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J

/-- Zero shift is a vanishing commutator, with both slots present. -/
theorem wardTraceSeries_slots_zero_shift
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ - 2) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    leftWardTraceSeries Y₁ Y₂ a x y (k - 1) n₁ n₂ J +
      rightWardTraceSeries Y₁ Y₂ a x y (k - 1) n₁ n₂ J = 0 := by
  rw [← wardTraceSeries_eq_slots]
  ext n
  simpa only [wardTraceSeries, PowerSeries.coeff_mk, map_zero] using
    wardTrace_zero_shift Y₁ Y₂ ha hx hy n₁ n₂ hn J hJ
      (N.h - W.centralCharge / 24 + n)

/-- The exceptional conformal mode is the energy term, not an inverse of
`1-q^0`. This identity still has an uncollected first-slot commutator. -/
theorem trace_middle_omega_energy
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (n₁ n₂ : ℂ) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      W.conformalVector x y J) :
    operatorTraceSeries N ((Y₁.val n₁ x).comp
      ((mode (Q.isMod.YM W.conformalVector) 1).comp (Y₂.val n₂ y))) =
      FuchsianODE.thetaShift (N.h - W.centralCharge / 24)
        (operatorTraceSeries N ((Y₁.val n₁ x).comp (Y₂.val n₂ y))) +
      (W.centralCharge / 24) •
        operatorTraceSeries N ((Y₁.val n₁ x).comp (Y₂.val n₂ y)) -
      leftWardTraceSeries Y₁ Y₂ W.conformalVector x y 1 n₁ n₂ J := by
  rw [trace_middle_eq_left_sub Y₁ Y₂ W.conformalVector x y 1 n₁ n₂ J hJ]
  congr 1
  ext n
  simp only [coeff_operatorTraceSeries, gradedTraceOp_L0_mul, map_add,
    FuchsianODE.coeff_thetaShift, PowerSeries.coeff_smul, smul_eq_mul]
  ring

end VOA.Huang.GenusTwoPoint.Separate
