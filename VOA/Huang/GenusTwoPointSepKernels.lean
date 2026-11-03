import VOA.Huang.GenusTwoPointSepSeries
import VOA.Huang.GenusTwoPointElliptic

/-!
# Explicit product-chart Fourier coefficient bounds

In the chart `q = x*y`, the positive Fourier monomials have indices
`(r*l, r*(l+1))` and the negative ones `(r*(l+1), r*l)`.
Thus each off-diagonal coefficient involves at most one Fourier mode `r`.
The explicit arrays below have polynomial coefficient bounds, and their
four-generator algebra has jointly subexponential coefficients.

Identification of the elliptic arrays with the analytic Fourier sums and then
with the lattice kernels is not asserted. The Eisenstein identification is
proved. These distinctions matter when specializing a formal trace map.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.HuangODEThree QEquation
open scoped BigOperators

/-- The positive/negative Fourier-mode array, without normalization constants.
The positive part includes the q-constant rational term. -/
def ellipticArray (d i j : ℕ) : ℂ :=
  if i < j ∧ (j - i) ∣ i then ((j - i : ℕ) : ℂ) ^ d
  else if j < i ∧ (i - j) ∣ j then -(-1 : ℂ) ^ d * ((i - j : ℕ) : ℂ) ^ d
  else 0

theorem ellipticArray_bound (d i j : ℕ) :
    ‖ellipticArray d i j‖ ≤ ((i + j : ℕ) : ℝ) ^ d := by
  unfold ellipticArray
  split_ifs
  · simp only [norm_pow, Complex.norm_natCast]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show j - i ≤ i + j by omega)) _
  · simp only [norm_mul, norm_neg, norm_pow, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show i - j ≤ i + j by omega)) _
  · simp only [norm_zero]; positivity

theorem ellipticArray_joint (d : ℕ) : JointSubexponential (ellipticArray d) := by
  intro r hr
  obtain ⟨C, hC⟩ := subexponential_pow d r hr
  exact ⟨C, fun i j => (ellipticArray_bound d i j).trans (hC (i + j))⟩

/-- A check of the q-constant term, valid for all orders including zero. -/
theorem ellipticArray_zero_left (d j : ℕ) :
    ellipticArray d 0 j = if j = 0 then 0 else (j : ℂ) ^ d := by
  by_cases hj : j = 0
  · simp [hj, ellipticArray]
  · simp [ellipticArray, hj, Nat.pos_of_ne_zero hj]

/-- No negative product-chart powers occur in an individual Lambert monomial.
The cancellation is only asserted where the original inverse is defined. -/
theorem inverse_monomial_chart (x y : ℂ) (hy : y ≠ 0) (r l : ℕ) :
    (y⁻¹) ^ r * (x * y) ^ (r * (l + 1)) =
      x ^ (r * (l + 1)) * y ^ (r * l) := by
  rw [mul_pow, Nat.mul_add, Nat.mul_one, pow_add y, inv_pow]
  have h : (y ^ r)⁻¹ * y ^ r = 1 := inv_mul_cancel₀ (pow_ne_zero _ hy)
  calc
    _ = ((y ^ r)⁻¹ * y ^ r) * (x ^ (r * l + r) * y ^ (r * l)) := by ring
    _ = _ := by rw [h, one_mul]

def ellipticSeries (d : ℕ) : BiSeries := ofArray (ellipticArray d)

theorem ellipticSeries_mem (d : ℕ) : ellipticSeries d ∈ bidiscAlgebra := by
  change JointSubexponential (coeff (ofArray (ellipticArray d)))
  rw [coeff_ofArray_fun]
  exact ellipticArray_joint d

/-- Eisenstein q-series pulled back along `q = x*y`. -/
def eisensteinSeries (j : ℕ) : BiSeries := ofArray fun i k =>
  if i = k then (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * j) * zhuG j i else 0

theorem eisensteinSeries_mem (j : ℕ) : eisensteinSeries j ∈ bidiscAlgebra := by
  intro r hr
  obtain ⟨C, hC⟩ := subexponential_zhuG j r hr
  have hC0 : 0 ≤ C := (norm_nonneg (zhuG j 0)).trans
    (by simpa only [pow_zero, mul_one] using hC 0)
  refine ⟨‖(2 * (Real.pi : ℂ) * Complex.I) ^ (2 * j)‖ * C, fun i k => ?_⟩
  simp only [eisensteinSeries, coeff_ofArray]
  split_ifs with hik
  · rw [norm_mul]
    calc
      _ ≤ ‖(2 * (Real.pi : ℂ) * Complex.I) ^ (2 * j)‖ * (C * r ^ i) := by
        gcongr
        exact hC i
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hr.le (Nat.le_add_right i k)) (by positivity)
  · simp only [norm_zero]; positivity

def wpTwoSeries : BiSeries :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • ellipticSeries 1 - eisensteinSeries 1

def wpThreeSeries : BiSeries :=
  (-((2 * (Real.pi : ℂ) * Complex.I) ^ 3 / 2)) • ellipticSeries 2

def fourierGenerators : Fin 4 → BiSeries :=
  ![eisensteinSeries 2, eisensteinSeries 3, wpTwoSeries, wpThreeSeries]

theorem fourierGenerators_mem (k : Fin 4) : fourierGenerators k ∈ bidiscAlgebra := by
  fin_cases k
  · exact eisensteinSeries_mem 2
  · exact eisensteinSeries_mem 3
  · exact bidiscAlgebra.sub_mem (bidiscAlgebra.smul_mem (ellipticSeries_mem 1) _)
      (eisensteinSeries_mem 1)
  · exact bidiscAlgebra.smul_mem (ellipticSeries_mem 2) _

/-- Whole-bidisc bounds for every algebraic coefficient, not merely a germ at q=0. -/
theorem fourierCoefficient_bound (a : coefficientAlgebra fourierGenerators)
    {r : ℝ} (hr : 1 < r) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ i j, ‖coeff a.val i j‖ ≤ G * r ^ i * r ^ j := by
  obtain ⟨G, hG0, hG⟩ := joint_bound
    (coefficientAlgebra_le_bidisc fourierGenerators fourierGenerators_mem a.property) hr
  exact ⟨G, hG0, fun i j => by simpa [pow_add, mul_assoc] using hG i j⟩

/-- Absolute convergence of each coefficient-ring element on the product bidisc. -/
theorem fourierCoefficient_summable (a : coefficientAlgebra fourierGenerators)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖coeff a.val p.1 p.2 * x ^ p.1 * y ^ p.2‖) :=
  summable_of_jointSubexponential
    (coefficientAlgebra_le_bidisc fourierGenerators fourierGenerators_mem a.property) hx hy

/-- The diagonal Eisenstein array is the actual q-function in the product chart. -/
theorem eisensteinSeries_eval (j : ℕ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' p : ℕ × ℕ, coeff (eisensteinSeries j) p.1 p.2 * x ^ p.1 * y ^ p.2) =
      huangEisensteinQ j (x * y) := by
  have hs := Summable.of_norm (summable_of_jointSubexponential (eisensteinSeries_mem j) hx hy)
  rw [hs.tsum_prod' (fun i => hs.prod_factor i)]
  unfold huangEisensteinQ eisensteinQ
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp only [eisensteinSeries, coeff_ofArray, ite_true, mul_pow]
    ring
  · intro k hk
    simp [eisensteinSeries, coeff_ofArray, Ne.symm hk]

end VOA.Huang.GenusTwoPoint.Separate
