import VOA.Huang.GenusTwoPointSepSpatialEvaluation

/-!
# Three-variable raw trace coefficients

`SpatialDistribution` records coefficients of x₁^a t^b, where t=x₂/x₁.
Exponents may be complex. It is an additive space, not an unrestricted
convolution ring: products of arbitrary distributions need not exist.
The remaining q variable is a genuine power series. Every coefficient of
the actual trace is a finite-dimensional trace. No spatial sum is taken.

The normal-order identities below still have binomial/geometric coefficients;
they are NOT the elliptically collected minus-two Ward identities.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module QEquation
open scoped BigOperators

/-- Coefficients of x₁^a t^b, without an invalid unrestricted convolution product. -/
abbrev SpatialDistribution := ℂ → ℂ → ℂ

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Raw formal trace. The powers determine both intertwiner modes uniquely. -/
def rawSpatialTrace
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) : ℂ → ℂ → PowerSeries ℂ :=
  fun a b => operatorTraceSeries N ((Y₁.val (b - a - 1) x).comp (Y₂.val (-b - 1) y))

@[simp] theorem coeff_rawSpatialTrace
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (n : ℕ) (a b : ℂ) :
    PowerSeries.coeff n (rawSpatialTrace Y₁ Y₂ x y a b) =
      productModeTrace Y₁ Y₂ x y (b - a - 1) (-b - 1)
        (N.h - W.centralCharge / 24 + n) := by
  simp [rawSpatialTrace, productModeTrace]

/-- Each monomial coefficient is a finite sum on the traced weight space. -/
theorem rawSpatialTrace_finite_coeff
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (n : ℕ) (a b : ℂ)
    {ι : Type*} [Fintype ι] (e : Basis ι ℂ (N.isMod.weight (N.h + n))) :
    PowerSeries.coeff n (rawSpatialTrace Y₁ Y₂ x y a b) =
      ∑ j, MatrixCoeff.prodCoeff Y₁.val Y₂.val
        (weightFunctional N.isMod (N.h + n) e j) x y (e j) (b - a - 1) (-b - 1) := by
  rw [coeff_rawSpatialTrace]
  convert productModeTrace_eq_sum Y₁ Y₂ x y (b - a - 1) (-b - 1) (N.h + n) e using 1
  congr 1
  ring

/-- Weight conservation fixes x₁'s exponent, before any evaluation. -/
theorem rawSpatialTrace_total_support
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {a : ℂ} (ha : a ≠ -α₁ - α₂) (b : ℂ) :
    rawSpatialTrace Y₁ Y₂ x y a b = 0 := by
  ext n
  rw [coeff_rawSpatialTrace, map_zero]
  apply productModeTrace_eq_zero Y₁ Y₂ hx hy
  intro h
  apply ha
  linear_combination -h

/-- At each q-degree the t-support is a single bounded-below progression.
Fixing t's exponent therefore pins the intermediate level. -/
theorem rawSpatialTrace_intermediate_support
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₂ : ℂ} (x : P₁.carrier) {y : P₂.carrier}
    (hy : y ∈ P₂.isMod.weight α₂) (n : ℕ) (a b : ℂ)
    (hb : ∀ k : ℕ, b ≠ Q.h - N.h - α₂ + k - n) :
    PowerSeries.coeff n (rawSpatialTrace Y₁ Y₂ x y a b) = 0 := by
  rw [coeff_rawSpatialTrace]
  have he : N.h - W.centralCharge / 24 + (n : ℂ) =
      (N.h + n) - W.centralCharge / 24 := by ring
  rw [he]
  apply productModeTrace_eq_zero_of_off_coset Y₁ Y₂ x hy
  intro k h
  apply hb k
  linear_combination -h

/-- The solved left-boundary series, with the zero mode retained as in the middle. -/
def transportedLeftSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (k i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  transportedMiddleSeries Y₁ Y₂ a x y k i n₁ n₂ J +
    leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J

theorem trace_left_eq_transported
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (i : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N
      (mode (N.isMod.YM a) i * ((Y₁.val n₁ x).comp (Y₂.val n₂ y))) =
      transportedLeftSeries Y₁ Y₂ a x y k i n₁ n₂ J := by
  rw [transportedLeftSeries, ← trace_middle_eq_transported Y₁ Y₂ ha hx hy i n₁ n₂ hn J hJ,
    trace_middle_eq_left_sub Y₁ Y₂ a x y i n₁ n₂ J hJ, sub_add_cancel]

/-- Left normal ordering, with both nonzero transport shifts solved. -/
theorem trace_product_mode_iterate_left_transport
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (ell : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - ell - 3) (n : ℕ) :
    ∃ J I : ℕ, TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J ∧
      productModeTrace Y₁ Y₂ (mode (P₁.isMod.YM a) ell x) y n₁ n₂
        (N.h - W.centralCharge / 24 + n) =
      ∑ i ∈ Finset.range I, (negOnePow i * cbz ell i) *
        (PowerSeries.coeff n
            (transportedLeftSeries Y₁ Y₂ a x y k (ell - i) (n₁ + i) n₂ J) -
          negOnePow ell * PowerSeries.coeff n
            (transportedMiddleSeries Y₁ Y₂ a x y k i (ell + n₁ - i) n₂ J)) := by
  obtain ⟨J, hJ⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y
  obtain ⟨I, hI⟩ := trace_product_mode_iterate Y₁ Y₂ hx hy a ell n₁ n₂
    (N.h - W.centralCharge / 24 + n)
  refine ⟨J, I, hJ, hI.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := congrArg (PowerSeries.coeff n)
    (trace_left_eq_transported Y₁ Y₂ ha hx hy (ell - i) (n₁ + i) n₂
      (by push_cast; linear_combination hn) J hJ)
  have h₂ := congrArg (PowerSeries.coeff n)
    (trace_middle_eq_transported Y₁ Y₂ ha hx hy i (ell + n₁ - i) n₂
      (by push_cast; linear_combination hn) J hJ)
  rw [coeff_operatorTraceSeries] at h₁ h₂
  rw [← h₁, ← h₂]

/-- The raw left identity as a simultaneous identity in q and both spatial
exponents on its weight-conservation line. Each coefficient sum is finite. -/
theorem rawSpatialTrace_left_normalOrder
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (ell : ℤ) :
    ∃ J I : ℂ → ℕ → ℕ, ∀ b : ℂ,
      rawSpatialTrace Y₁ Y₂ (mode (P₁.isMod.YM a) ell x) y
        (-α₁ - α₂ - k + ell + 1) b =
      PowerSeries.mk (fun n =>
        ∑ i ∈ Finset.range (I b n), (negOnePow i * cbz ell i) *
          (PowerSeries.coeff n (transportedLeftSeries Y₁ Y₂ a x y k (ell - i)
              (b - (-α₁ - α₂ - k + ell + 1) - 1 + i) (-b - 1) (J b n)) -
            negOnePow ell * PowerSeries.coeff n
              (transportedMiddleSeries Y₁ Y₂ a x y k i
                (ell + (b - (-α₁ - α₂ - k + ell + 1) - 1) - i) (-b - 1) (J b n)))) := by
  have h := fun b n => trace_product_mode_iterate_left_transport Y₁ Y₂ ha hx hy ell
    (b - (-α₁ - α₂ - k + ell + 1) - 1) (-b - 1) (by ring) n
  choose J I _ hI using h
  exact ⟨J, I, fun b => by ext n; simpa using hI b n⟩

/-- The opposite normal order uses its own q-shift factors. -/
theorem rawSpatialTrace_right_normalOrder
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (ell : ℤ) :
    ∃ J I : ℂ → ℕ → ℕ, ∀ b : ℂ,
      rawSpatialTrace Y₁ Y₂ x (mode (P₂.isMod.YM a) ell y)
        (-α₁ - α₂ - k + ell + 1) b =
      PowerSeries.mk (fun n =>
        ∑ i ∈ Finset.range (I b n), (negOnePow i * cbz ell i) *
          (PowerSeries.coeff n (transportedMiddleSeries Y₁ Y₂ a x y k (ell - i)
              (b - (-α₁ - α₂ - k + ell + 1) - 1) (-b - 1 + i) (J b n)) -
            negOnePow ell * PowerSeries.coeff n
              (transportedRightSeries Y₁ Y₂ a x y k i
                (b - (-α₁ - α₂ - k + ell + 1) - 1) (ell + (-b - 1) - i) (J b n)))) := by
  have h := fun b n => trace_product_mode_iterate_right_transport Y₁ Y₂ ha hx hy ell
    (b - (-α₁ - α₂ - k + ell + 1) - 1) (-b - 1) (by ring) n
  choose J I _ hI using h
  exact ⟨J, I, fun b => by ext n; simpa using hI b n⟩

/-- The zero-mode energy identity before spatial evaluation, including c/24. -/
theorem rawSpatialTrace_middle_energy
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (a b : ℂ) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule
      W.conformalVector x y J) :
    operatorTraceSeries N ((Y₁.val (b - a - 1) x).comp
      ((mode (Q.isMod.YM W.conformalVector) 1).comp (Y₂.val (-b - 1) y))) =
      FuchsianODE.thetaShift (N.h - W.centralCharge / 24) (rawSpatialTrace Y₁ Y₂ x y a b) +
        (W.centralCharge / 24) • rawSpatialTrace Y₁ Y₂ x y a b -
        leftWardTraceSeries Y₁ Y₂ W.conformalVector x y 1 (b - a - 1) (-b - 1) J :=
  trace_middle_omega_energy Y₁ Y₂ x y (b - a - 1) (-b - 1) J hJ

end VOA.Huang.GenusTwoPoint.Separate
