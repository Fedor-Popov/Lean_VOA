import VOA.Huang.GenusTwoPointSepCoordinateScalar
import VOA.Modularity.SquareBracketSubst

/-! # Realization of the scalar flow by formal power-series differentiation -/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open scoped BigOperators

/-- D^r z, represented as a formal power series with zero constant coefficient. -/
def flowSeries (a : ℕ → ℂ) (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.mk (flowCoeff a r)

@[simp] theorem coeff_flowSeries (a : ℕ → ℂ) (r n : ℕ) :
    PowerSeries.coeff (n + 1) (flowSeries a r) = flowCoeff a r n := by
  simp [flowSeries, PowerSeries.coeff_succ_X_mul]

@[simp] theorem flowSeries_zero (a : ℕ → ℂ) : flowSeries a 0 = PowerSeries.X := by
  ext n
  cases n with
  | zero => simp [flowSeries]
  | succ n => simp [coeff_flowSeries, flowCoeff, PowerSeries.coeff_X]

/-- The scalar recursion is exactly iteration of the formal vector field,
using Mathlib's power-series derivative, rather than an assumed flow identity. -/
theorem flowSeries_succ (a : ℕ → ℂ) (r : ℕ) :
    flowSeries a (r + 1) = PowerSeries.X ^ 2 *
      ((PowerSeries.derivative ℂ) (flowSeries a r) * PowerSeries.mk a) := by
  ext n
  cases n with
  | zero => simp [flowSeries, pow_two, mul_assoc]
  | succ n =>
    rw [coeff_flowSeries, flowCoeff, pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul]
    cases n with
    | zero => simp
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro j _
      simp only [PowerSeries.coeff_derivative, coeff_flowSeries, PowerSeries.coeff_mk,
        Nat.add_sub_cancel]
      ring

/-- The coefficientwise exponential applied to the coordinate z. -/
def flowExponential (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.mk (flowExpCoeff a)

/-- The normalized logarithmic coordinate, expressed directly in Mathlib's log. -/
theorem flowExponential_log :
    flowExponential (iterativeLog (logarithmicCoordinate 1)) = PowerSeries.log ℂ := by
  ext n
  cases n with
  | zero => simp [flowExponential]
  | succ n =>
    rw [flowExponential, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    cases n with
    | zero => simp [PowerSeries.coeff_log]
    | succ n =>
      rw [iterativeLog_equation]
      simp only [logarithmicCoordinate, PowerSeries.coeff_log, eq_ratCast]
      push_cast
      simp only [pow_succ]
      ring

/-- Explicit use of the repository's Zhu coordinate substitution theorem. -/
theorem flowExponential_subst_expMinusOne :
    (flowExponential (iterativeLog (logarithmicCoordinate 1))).subst expMinusOne =
      PowerSeries.X := by
  rw [flowExponential_log]
  exact log_subst_expMinusOne

/-- Scaling the coordinate scales the j-th generator coefficient by c^j. -/
def scaleGenerator (c : ℂ) (a : ℕ → ℂ) (j : ℕ) : ℂ := c ^ (j + 1) * a j

theorem flowCoeff_scale (c : ℂ) (a : ℕ → ℂ) (r n : ℕ) :
    flowCoeff (scaleGenerator c a) r n = c ^ n * flowCoeff a r n := by
  induction r generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [flowCoeff, hn]
  | succ r ih =>
    simp only [flowCoeff, ih, scaleGenerator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have he : j + (n - 1 - j + 1) = n := by omega
    calc
      _ = (c ^ j * c ^ (n - 1 - j + 1)) *
        (((j : ℂ) + 1) * flowCoeff a r j * a (n - 1 - j)) := by ring
      _ = _ := by rw [← pow_add, he]

theorem flowExpCoeff_scale (c : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    flowExpCoeff (scaleGenerator c a) n = c ^ n * flowExpCoeff a n := by
  simp only [flowExpCoeff, flowCoeff_scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Huang's A_j = (2*pi*i)^j B_j, where B generates log(1+z). -/
theorem iterativeLog_logarithmic_scale (c : ℂ) :
    iterativeLog (logarithmicCoordinate c) =
      scaleGenerator c (iterativeLog (logarithmicCoordinate 1)) := by
  symm
  apply iterativeLog_unique
  intro n
  rw [flowExpCoeff_scale, iterativeLog_equation]
  simp only [logarithmicCoordinate]
  rw [show -c = c * (-1) by ring, mul_pow]
  ring

/-- The full Huang defining coordinate, including the chosen 2*pi*i scale. -/
theorem huangA_scale : huangA = scaleGenerator (2 * (Real.pi : ℂ) * Complex.I)
    (iterativeLog (logarithmicCoordinate 1)) :=
  iterativeLog_logarithmic_scale _

/-- Scalar rescaling of the full coordinate exponential, including degree one. -/
theorem flowExponential_scale (c : ℂ) (a : ℕ → ℂ) :
    c • flowExponential (scaleGenerator c a) = PowerSeries.rescale c (flowExponential a) := by
  ext n
  cases n with
  | zero => simp [flowExponential]
  | succ n =>
    simp only [PowerSeries.coeff_smul, flowExponential, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_rescale, flowExpCoeff_scale, smul_eq_mul]
    rw [pow_succ]
    ring

/-- Huang's defining normalized logarithm in Mathlib's formal power-series API. -/
theorem huangA_formal_log :
    (2 * (Real.pi : ℂ) * Complex.I) • flowExponential huangA =
      PowerSeries.rescale (2 * (Real.pi : ℂ) * Complex.I) (PowerSeries.log ℂ) := by
  rw [huangA_scale, flowExponential_scale, flowExponential_log]

end VOA.Huang.GenusTwoPoint.Separate
