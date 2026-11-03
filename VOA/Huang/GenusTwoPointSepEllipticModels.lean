import VOA.Huang.GenusTwoPointSepEllipticEvaluation

/-!
# The product-chart generators evaluate to the existing Fourier kernel models

These comparisons identify `wpTwoSeries` and `wpThreeSeries` with `wpTwoQ`
and `wpThreeQ`. They do not identify the Fourier models with lattice functions
and do not establish a trace Ward identity.
-/

noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.HuangODEThree QEquation
open scoped BigOperators

theorem summable_elliptic_constant (d : ℕ) {y : ℂ} (hy : ‖y‖ < 1) :
    Summable (fun r : ℕ => (r + 1 : ℂ) ^ d * y ^ (r + 1)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (summable_pow_mul_geometric_of_norm_lt_one d hy)

/-- Splitting off the q-constant term gives the library's Lambert-tail model. -/
theorem ellipticSeries_eval_lambert (d : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hy₀ : y ≠ 0) :
    (∑' p : ℕ × ℕ, coeff (ellipticSeries d) p.1 p.2 * x ^ p.1 * y ^ p.2) =
      (∑' r : ℕ, (r + 1 : ℂ) ^ d * y ^ (r + 1)) +
        lambertTail (ellipticCoeff d y) (x * y) := by
  have hxy : ‖x * y‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hden (r : ℕ) : 1 - (x * y) ^ (r + 1) ≠ 0 := by
    have hp : ‖(x * y) ^ (r + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hxy (by omega)
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hp
    exact lt_irrefl _ hp
  have he (r : ℕ) :
      (r + 1 : ℂ) ^ d * y ^ (r + 1) +
        ellipticCoeff d y r * (x * y) ^ (r + 1) / (1 - (x * y) ^ (r + 1)) =
      (r + 1 : ℂ) ^ d * y ^ (r + 1) / (1 - (x * y) ^ (r + 1)) -
        (-1 : ℂ) ^ d * ((r + 1 : ℂ) ^ d * x ^ (r + 1) /
          (1 - (x * y) ^ (r + 1))) := by
    rw [← mul_div_assoc]
    apply (mul_right_cancel₀ (hden r))
    simp only [add_mul, sub_mul, div_mul_cancel₀ _ (hden r)]
    unfold ellipticCoeff
    simp only [inv_pow, mul_pow]
    field_simp [pow_ne_zero _ hy₀]
    ring
  have hf := (summable_positiveEllipticFourier d hx hy).sub
    (by simpa [mul_comm y x] using
      ((summable_positiveEllipticFourier d hy hx).mul_left ((-1 : ℂ) ^ d)))
  have hb := summable_elliptic_constant d hy
  have ht : Summable (fun r : ℕ =>
      ellipticCoeff d y r * (x * y) ^ (r + 1) / (1 - (x * y) ^ (r + 1))) := by
    apply (hf.sub hb).congr
    intro r
    linear_combination -(he r)
  rw [ellipticSeries_eval_fourier d hx hy, lambertTail, ← hb.tsum_add ht]
  apply tsum_congr
  intro r
  rw [he r]
  ring

/-- The rational q-constant term of the even kernel. -/
theorem elliptic_constant_one {y : ℂ} (hy : ‖y‖ < 1) :
    (∑' r : ℕ, (r + 1 : ℂ) ^ 1 * y ^ (r + 1)) = y / (1 - y) ^ 2 := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hy).mul_right y
  convert h.tsum_eq using 1
  · apply tsum_congr
    intro r
    simp [pow_succ, mul_assoc]
  · ring

/-- The rational q-constant term of the odd kernel. -/
theorem elliptic_constant_two {y : ℂ} (hy : ‖y‖ < 1) :
    (∑' r : ℕ, (r + 1 : ℂ) ^ 2 * y ^ (r + 1)) = y * (1 + y) / (1 - y) ^ 3 := by
  have h₂ := ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hy).mul_left (2 : ℂ)).mul_right y
  have h₁ := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hy).mul_right y
  have he (r : ℕ) : 2 * ((r + 2).choose 2 : ℂ) - (r + 1) = (r + 1 : ℂ) ^ 2 := by
    have hn := Nat.add_one_mul_choose_eq (r + 1) 1
    simp only [Nat.choose_one_right] at hn
    have hc : ((r + 1 : ℂ) + 1) * (r + 1) = ((r + 2).choose 2 : ℂ) * 2 := by
      exact_mod_cast hn
    linear_combination -hc
  have hsum := (h₂.sub h₁).tsum_eq
  have hn : 1 - y ≠ 0 := by
    intro hn
    rw [← sub_eq_zero.mp hn, norm_one] at hy
    exact lt_irrefl _ hy
  calc
    _ = ∑' r : ℕ, ((2 * (((r + 2).choose 2 : ℂ) * y ^ r)) * y -
        (((r + 1).choose 1 : ℂ) * y ^ r) * y) := by
      apply tsum_congr
      intro r
      rw [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, ← he r, pow_succ]
      ring
    _ = _ := by
      rw [hsum]
      norm_num
      field_simp
      ring

/-- Exact comparison with the already defined even Fourier kernel. -/
theorem wpTwoSeries_eval {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hy₀ : y ≠ 0) :
    (∑' p : ℕ × ℕ, coeff wpTwoSeries p.1 p.2 * x ^ p.1 * y ^ p.2) =
      wpTwoQ y (x * y) := by
  have hs := (Summable.of_norm
    (summable_of_jointSubexponential (ellipticSeries_mem 1) hx hy)).mul_left
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)
  have ht := Summable.of_norm
    (summable_of_jointSubexponential (eisensteinSeries_mem 1) hx hy)
  have he (p : ℕ × ℕ) : coeff wpTwoSeries p.1 p.2 * x ^ p.1 * y ^ p.2 =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
        (coeff (ellipticSeries 1) p.1 p.2 * x ^ p.1 * y ^ p.2) -
      coeff (eisensteinSeries 1) p.1 p.2 * x ^ p.1 * y ^ p.2 := by
    simp only [wpTwoSeries, coeff, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
    ring
  simp_rw [he]
  rw [hs.tsum_sub ht, tsum_mul_left, ellipticSeries_eval_lambert 1 hx hy hy₀,
    elliptic_constant_one hy, eisensteinSeries_eval 1 hx hy]
  rfl

/-- Exact comparison with the already defined odd Fourier kernel. -/
theorem wpThreeSeries_eval {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hy₀ : y ≠ 0) :
    (∑' p : ℕ × ℕ, coeff wpThreeSeries p.1 p.2 * x ^ p.1 * y ^ p.2) =
      wpThreeQ y (x * y) := by
  have he (p : ℕ × ℕ) : coeff wpThreeSeries p.1 p.2 * x ^ p.1 * y ^ p.2 =
      (-((2 * (Real.pi : ℂ) * Complex.I) ^ 3 / 2)) *
        (coeff (ellipticSeries 2) p.1 p.2 * x ^ p.1 * y ^ p.2) := by
    simp only [wpThreeSeries, coeff_smul]
    ring
  simp_rw [he]
  rw [tsum_mul_left, ellipticSeries_eval_lambert 2 hx hy hy₀, elliptic_constant_two hy]
  rfl

end VOA.Huang.GenusTwoPoint.Separate
