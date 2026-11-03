import VOA.Huang.GenusOneIntCoordBracketReduction

/-!
# Absolute scalar majorant for logarithmic re-expansion

The coefficients of `(exp y - 1)^k` are nonnegative real numbers.
Consequently their absolute sum at a complex argument is exactly
`(Real.exp ‖y‖ - 1)^k`. This is an absolute, ungrouped estimate.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open scoped BigOperators

theorem expSubOneCoeff_eq_coeff (k r : ℕ) :
    expSubOneCoeff k r =
      PowerSeries.coeff r ((PowerSeries.exp ℂ - 1) ^ k) := by
  rw [sub_eq_add_neg, add_pow, map_sum]
  simp only [expSubOneCoeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (-1 : PowerSeries ℂ) = PowerSeries.C (-1 : ℂ) by simp,
    show (k.choose i : PowerSeries ℂ) = PowerSeries.C (k.choose i : ℂ) by simp,
    ← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C,
    PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  push_cast
  ring

theorem expSubOneCoeff_eq_real (k r : ℕ) :
    expSubOneCoeff k r =
      Complex.ofReal (PowerSeries.coeff r ((PowerSeries.exp ℝ - 1) ^ k)) := by
  rw [expSubOneCoeff_eq_coeff]
  simpa using PowerSeries.coeff_map Complex.ofRealHom r ((PowerSeries.exp ℝ - 1) ^ k)

theorem expSubOne_real_nonneg (k r : ℕ) :
    0 ≤ PowerSeries.coeff r ((PowerSeries.exp ℝ - 1) ^ k) := by
  induction k generalizing r with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg (ih _)
    cases p.2 with
    | zero => simp
    | succ n => simp [PowerSeries.coeff_exp]

theorem norm_expSubOneCoeff (k r : ℕ) :
    ‖expSubOneCoeff k r‖ =
      PowerSeries.coeff r ((PowerSeries.exp ℝ - 1) ^ k) := by
  rw [expSubOneCoeff_eq_real, Complex.norm_real,
    Real.norm_of_nonneg (expSubOne_real_nonneg k r)]

theorem hasSum_norm_expSubOneCoeff (k : ℕ) (y : ℂ) :
    HasSum (fun r : ℕ => ‖expSubOneCoeff k r * y ^ r‖)
      ((Real.exp ‖y‖ - 1) ^ k) := by
  have hs := Complex.reCLM.hasSum (hasSum_expSubOneCoeff k (‖y‖ : ℂ))
  convert hs using 1
  · ext r
    rw [norm_mul, norm_pow, norm_expSubOneCoeff, expSubOneCoeff_eq_real]
    simp [← Complex.ofReal_pow]
  · simp [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_pow]

/-- Tonelli reduces the triple absolute sum to an ordinary positive series.
The hypothesis concerns each square-component row separately, not its sum. -/
theorem summable_expSubOneCoeff_mul_iff (a : ℕ → ℕ → ℂ)
    (ha : ∀ k, Summable (fun n => ‖a k n‖)) (y : ℂ) :
    Summable (fun p : ℕ × (ℕ × ℕ) =>
      expSubOneCoeff p.1 p.2.2 * y ^ p.2.2 * a p.1 p.2.1) ↔
    Summable (fun k => (Real.exp ‖y‖ - 1) ^ k * ∑' n, ‖a k n‖) := by
  let f : ℕ × (ℕ × ℕ) → ℝ := fun p =>
    ‖expSubOneCoeff p.1 p.2.2 * y ^ p.2.2 * a p.1 p.2.1‖
  have hscalar (k n : ℕ) : HasSum (fun r => f (k, n, r))
      ((Real.exp ‖y‖ - 1) ^ k * ‖a k n‖) := by
    simpa only [f, norm_mul] using (hasSum_norm_expSubOneCoeff k y).mul_right ‖a k n‖
  have hrow (k : ℕ) : Summable (fun p : ℕ × ℕ => f (k, p)) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => f (k, p))
      (fun _ => norm_nonneg _)).mpr
    refine ⟨fun n => (hscalar k n).summable, ?_⟩
    simpa only [(hscalar k _).tsum_eq] using (ha k).mul_left ((Real.exp ‖y‖ - 1) ^ k)
  have hsum (k : ℕ) : (∑' p : ℕ × ℕ, f (k, p)) =
      (Real.exp ‖y‖ - 1) ^ k * ∑' n, ‖a k n‖ := by
    rw [(hrow k).tsum_prod]
    simp_rw [(hscalar k _).tsum_eq]
    exact tsum_mul_left
  rw [← summable_norm_iff]
  change Summable f ↔ _
  rw [summable_prod_of_nonneg (f := f) (fun _ => norm_nonneg _)]
  simp only [hsum]
  exact and_iff_right hrow

/-- The absolute scalar re-expansion parameter tends to zero with `z`. -/
theorem exists_logMajorant_radius {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      Real.exp ‖Complex.log (1 + z)‖ - 1 < R := by
  have hc : ContinuousAt (fun z : ℂ => Real.exp ‖Complex.log (1 + z)‖ - 1) 0 := by
    apply ContinuousAt.sub _ continuousAt_const
    apply Real.continuous_exp.continuousAt.comp
    apply ContinuousAt.norm
    apply ContinuousAt.clog (continuousAt_const.add continuousAt_id)
    simp
  have he := hc.eventually (gt_mem_nhds (by simpa using hR))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun z hz => hd (by simpa [dist_zero_right] using hz)⟩

end VOA.Huang.GenusOne.IntCoord
