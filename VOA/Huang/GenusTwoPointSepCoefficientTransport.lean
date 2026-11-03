import VOA.Huang.GenusTwoPointSepMiddleTransport
import VOA.Huang.GenusTwoPointSepSquareInsertion

/-!
# Coefficientwise reverse-slot normal ordering

All nonzero weight shifts in the right-slot Jacobi iterate are replaced by
the geometric solutions. The zero mode is explicitly retained. The cutoff
may depend on the traced grade; no spatial sum is interchanged here.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module QEquation
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Geometric solution for the middle insertion, retaining the zero mode. -/
def transportedMiddleSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (k i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  let L := leftWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J
  let R := rightWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J
  if 0 < k - i - 1 then
    -(geometricDenominator (k - i - 1).toNat * L) -
      PowerSeries.X ^ (k - i - 1).toNat * geometricDenominator (k - i - 1).toNat * R
  else if 0 < i - k + 1 then
    PowerSeries.X ^ (i - k + 1).toNat * geometricDenominator (i - k + 1).toNat * L +
      geometricDenominator (i - k + 1).toNat * R
  else
    operatorTraceSeries N
      (mode (N.isMod.YM a) i * ((Y₁.val n₁ x).comp (Y₂.val n₂ y))) - L

/-- The mode at the right trace boundary differs by the second-slot commutator. -/
def transportedRightSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (x : P₁.carrier) (y : P₂.carrier)
    (k i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  transportedMiddleSeries Y₁ Y₂ a x y k i n₁ n₂ J -
    rightWardTraceSeries Y₁ Y₂ a x y i n₁ n₂ J

theorem trace_middle_eq_transported
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (i : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N ((Y₁.val n₁ x).comp
      ((mode (Q.isMod.YM a) i).comp (Y₂.val n₂ y))) =
      transportedMiddleSeries Y₁ Y₂ a x y k i n₁ n₂ J := by
  unfold transportedMiddleSeries
  split_ifs with hp hn'
  · exact trace_middle_q_transport_pos Y₁ Y₂ ha hx hy (by omega)
      (Int.toNat_of_nonneg (by omega)).symm n₁ n₂ hn J hJ
  · exact trace_middle_q_transport_neg Y₁ Y₂ ha hx hy (by omega)
      (Int.toNat_of_nonneg (by omega)).symm n₁ n₂ hn J hJ
  · exact trace_middle_eq_left_sub Y₁ Y₂ a x y i n₁ n₂ J hJ

theorem trace_right_eq_transported
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (i : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J) :
    operatorTraceSeries N
      (((Y₁.val n₁ x).comp (Y₂.val n₂ y)) * mode (N.isMod.YM a) i) =
      transportedRightSeries Y₁ Y₂ a x y k i n₁ n₂ J := by
  rw [transportedRightSeries, ← trace_middle_eq_transported Y₁ Y₂ ha hx hy i n₁ n₂ hn J hJ,
    trace_middle_eq_left_sub Y₁ Y₂ a x y i n₁ n₂ J hJ]
  have h := wardTraceSeries_eq Y₁ Y₂ a x y i n₁ n₂ J hJ
  rw [operatorTraceSeries_sub, wardTraceSeries_eq_slots] at h
  linear_combination h

/-- Right-slot insertion after solving every nonzero q-shift. In particular
`ell=-2` is allowed. Both finite cutoffs are genuine module truncation bounds. -/
theorem trace_product_mode_iterate_right_transport
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k : ℤ} {α₁ α₂ : ℂ} {a : V} {x : P₁.carrier} {y : P₂.carrier}
    (ha : a ∈ W.grading k) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (ell : ℤ) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - ell - 3) (n : ℕ) :
    ∃ J I : ℕ, TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J ∧
      productModeTrace Y₁ Y₂ x (mode (P₂.isMod.YM a) ell y) n₁ n₂
        (N.h - W.centralCharge / 24 + n) =
      ∑ i ∈ Finset.range I, (negOnePow i * cbz ell i) *
        (PowerSeries.coeff n
            (transportedMiddleSeries Y₁ Y₂ a x y k (ell - i) n₁ (n₂ + i) J) -
          negOnePow ell * PowerSeries.coeff n
            (transportedRightSeries Y₁ Y₂ a x y k i n₁ (ell + n₂ - i) J)) := by
  obtain ⟨J₁, hJ₁⟩ := P₁.isMod.truncation a x
  obtain ⟨J₂, hJ₂⟩ := P₂.isMod.truncation a y
  let J := (max J₁ J₂).toNat
  have hJ : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a x y J :=
    fun i hi => ⟨hJ₁ i (by dsimp [J] at hi; omega), hJ₂ i (by dsimp [J] at hi; omega)⟩
  obtain ⟨I, hI⟩ := trace_product_mode_iterate_right Y₁ Y₂ x hy a ell n₁ n₂
    (N.h - W.centralCharge / 24 + n)
  refine ⟨J, I, hJ, hI.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := congrArg (PowerSeries.coeff n)
    (trace_middle_eq_transported Y₁ Y₂ ha hx hy (ell - i) n₁ (n₂ + i)
      (by push_cast; linear_combination hn) J hJ)
  have h₂ := congrArg (PowerSeries.coeff n)
    (trace_right_eq_transported Y₁ Y₂ ha hx hy i n₁ (ell + n₂ - i)
      (by push_cast; linear_combination hn) J hJ)
  rw [coeff_operatorTraceSeries] at h₁ h₂
  rw [← h₁, ← h₂]
  rfl

/-- Formal geometric convolution, rescaled before taking a coefficient.
Only finitely many traced grades occur, without an analytic interchange. -/
theorem coeff_rescale_geometric_mul {d : ℕ} (hd : 0 < d)
    (rho : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.rescale rho (geometricDenominator d * F)) =
      rho ^ n * ∑ p ∈ Finset.antidiagonal n,
        if d ∣ p.1 then PowerSeries.coeff p.2 F else 0 := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
  simp only [coeff_geometricDenominator hd, ite_mul, one_mul, zero_mul]

/-- The transported numerator removes precisely the zero geometric term. -/
theorem coeff_rescale_shifted_geometric_mul {d : ℕ} (hd : 0 < d)
    (rho : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale rho (PowerSeries.X ^ d * geometricDenominator d * F)) =
      rho ^ n * (∑ p ∈ Finset.antidiagonal n,
        if d ∣ p.1 then PowerSeries.coeff p.2 F else 0) -
      rho ^ n * PowerSeries.coeff n F := by
  rw [← geometricDenominator_sub_one hd, sub_mul, one_mul, map_sub, map_sub,
    coeff_rescale_geometric_mul hd, PowerSeries.coeff_rescale]

/-- Collection remains coefficientwise finite after multiplying by a trace
series. No summability assumption on that formal trace series is needed. -/
theorem coeff_lambertCuspSeries_mul_geometric
    (c : ℕ → ℂ) (rho : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (lambertCuspSeries c rho * F) =
      ∑ k ∈ Finset.range n, PowerSeries.coeff n
        (PowerSeries.rescale rho
          (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1)) * F) := by
  have hcoeff (j : ℕ) (hj : j ≤ n) :
      PowerSeries.coeff j (lambertCuspSeries c rho) =
        ∑ k ∈ Finset.range n, PowerSeries.coeff j (PowerSeries.rescale rho
          (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1))) := by
    rw [coeff_lambertCuspSeries_geometric]
    apply finsum_eq_sum_of_support_subset
    intro k hk
    simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at *
    by_contra hn
    apply hk
    rw [PowerSeries.coeff_rescale, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero, mul_zero]
  rw [PowerSeries.coeff_mul]
  calc
    _ = ∑ p ∈ Finset.antidiagonal n, ∑ k ∈ Finset.range n,
        PowerSeries.coeff p.1 (PowerSeries.rescale rho
          (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1))) *
          PowerSeries.coeff p.2 F := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hcoeff p.1 (by have := Finset.mem_antidiagonal.mp hp; omega), Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact (PowerSeries.coeff_mul n _ F).symm

/-- Both elliptic orientations, including their q-shift, collected against
an arbitrary formal trace. The spatial constant term is kept as its existing
convergent inner-orientation sum when `norm x < 1`. -/
theorem coeff_ellipticCusp_trace_collection (d : ℕ) (x rho : ℂ)
    (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.C (∑' k : ℕ, (k + 1 : ℂ) ^ d * x ^ (k + 1)) +
        lambertCuspSeries (ellipticCoeff d x) rho) * F) =
      (∑' k : ℕ, (k + 1 : ℂ) ^ d * x ^ (k + 1)) * PowerSeries.coeff n F +
      ∑ k ∈ Finset.range n, PowerSeries.coeff n
        (PowerSeries.rescale rho
          (PowerSeries.C ((k + 1 : ℂ) ^ d *
            (x ^ (k + 1) - (-1 : ℂ) ^ d * (x⁻¹) ^ (k + 1))) *
            PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1)) * F) := by
  rw [add_mul, map_add, PowerSeries.coeff_C_mul, coeff_lambertCuspSeries_mul_geometric]
  rfl

end VOA.Huang.GenusTwoPoint.Separate
