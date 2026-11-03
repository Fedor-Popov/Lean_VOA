import VOA.Classification.COne.QExpWeightTwoEisenstein
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Convergence of the explicit weight-one Fourier series

The divisor formula from Mascot, Theorem 4.2.2,
https://doi.org/10.1007/s40993-022-00329-6, defines an actual convergent
function, without using a conditionally convergent lattice sum. Modularity
does not follow just from convergence and is not asserted here.
-/

open UpperHalfPlane Filter Topology
open scoped MatrixGroups Manifold

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem norm_weightOneDivisorCoeff_le {N : ℕ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (a b : Fin N) (n : ℕ) :
    ‖weightOneDivisorCoeff N ζ a b n‖ ≤ 2 * n := by
  have hp (m : ℕ) : ‖ζ ^ m‖ = 1 := by simp [norm_pow, hζ]
  have hi (p : Prop) [Decidable p] (m : ℕ) :
      ‖if p then ζ ^ m else 0‖ ≤ 1 := by split_ifs <;> simp [hp]
  calc
    _ ≤ ∑ t ∈ n.divisors, (2 : ℝ) := by
      apply norm_sum_le_of_le
      intro t ht
      have h1 := hi (t % N = a.val) ((n / t) * b.val)
      have h2 := hi ((t + a.val) % N = 0) ((n / t) * (N - b.val))
      exact (norm_sub_le _ _).trans (by linarith)
    _ = 2 * (n.divisors.card : ℝ) := by simp [mul_comm]
    _ ≤ 2 * n := by exact_mod_cast Nat.mul_le_mul_left 2 (Nat.card_divisors_le_self n)

/-- A linear majorant, with the constant coefficient kept explicit. -/
theorem norm_weightOneIntegralCoeff_le {N : ℕ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (a b : Fin N) (n : ℕ) :
    ‖weightOneIntegralCoeff N ζ a b n‖ ≤
      ‖weightOneIntegralCoeff N ζ a b 0‖ + 2 * ‖weightOneScale N ζ a b‖ * n := by
  by_cases hn : n = 0
  · subst n; simp
  by_cases hab : a.val = 0 ∧ b.val = 0
  · simp only [weightOneIntegralCoeff, if_pos hab, norm_zero]
    positivity
  · rw [weightOneIntegralCoeff, if_neg hab, if_neg hn, norm_mul]
    have h := mul_le_mul_of_nonneg_left (norm_weightOneDivisorCoeff_le hζ a b n)
      (norm_nonneg (weightOneScale N ζ a b))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      h.trans (le_add_of_nonneg_left (norm_nonneg _))

/-- Absolute convergence throughout the open unit disc. -/
theorem summable_weightOneIntegralCoeff {N : ℕ} {ζ q : ℂ} (hζ : ‖ζ‖ = 1)
    (a b : Fin N) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖weightOneIntegralCoeff N ζ a b n * q ^ n‖) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hng : Summable (fun n : ℕ => (n : ℝ) * ‖q‖ ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖(‖q‖ : ℝ)‖ < 1 by simpa using hq))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun n : ℕ => ‖weightOneIntegralCoeff N ζ a b 0‖ * ‖q‖ ^ n +
      (2 * ‖weightOneScale N ζ a b‖) * ((n : ℝ) * ‖q‖ ^ n))
  · intro n
    rw [norm_mul, norm_pow]
    have h := mul_le_mul_of_nonneg_right (norm_weightOneIntegralCoeff_le hζ a b n)
      (pow_nonneg (norm_nonneg q) n)
    simpa [add_mul, mul_assoc] using h
  · exact (hg.mul_left _).add (hng.mul_left _)

/-- The analytic candidate, expressed using width-N Fourier coefficients. -/
def weightOneQSeries (N : ℕ) (ζ : ℂ) (a b : Fin N) (τ : ℍ) : ℂ :=
  ∑' n : ℕ, weightOneIntegralCoeff N ζ a b n *
    Function.Periodic.qParam (N : ℝ) τ ^ n

theorem norm_qParam_nat_lt_one {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    ‖Function.Periodic.qParam (N : ℝ) τ‖ < 1 := by
  have : 0 < 2 * Real.pi * τ.im / (N : ℝ) := by positivity
  simpa [Function.Periodic.qParam, Complex.norm_exp, neg_div] using this

theorem hasSum_weightOneQSeries {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) (τ : ℍ) :
    HasSum (fun n : ℕ => weightOneIntegralCoeff N ζ a b n •
      Function.Periodic.qParam (N : ℝ) τ ^ n) (weightOneQSeries N ζ a b τ) := by
  simpa [weightOneQSeries, smul_eq_mul] using
    (summable_weightOneIntegralCoeff (hζ.norm'_eq_one hN.ne') a b
      (norm_qParam_nat_lt_one hN τ)).of_norm.hasSum

theorem weightOneIntegralCoeff_radius {N : ℕ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (a b : Fin N) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (weightOneIntegralCoeff N ζ a b)).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using
    summable_weightOneIntegralCoeff hζ a b
      (q := (r : ℂ)) (by simpa using hr)

/-- The sum is analytic on the whole open unit disc, including its center. -/
theorem analyticAt_weightOneDisc {N : ℕ} {ζ q : ℂ} (hζ : ‖ζ‖ = 1)
    (a b : Fin N) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (FormalMultilinearSeries.ofScalarsSum
      (weightOneIntegralCoeff N ζ a b) : ℂ → ℂ) q := by
  apply FormalMultilinearSeries.analyticOnNhd
  apply Metric.eball_subset_eball (weightOneIntegralCoeff_radius hζ a b)
  rw [← ENNReal.coe_one, Metric.eball_coe]
  simpa using hq

theorem weightOneQSeries_eq_disc (N : ℕ) (ζ : ℂ) (a b : Fin N) (τ : ℍ) :
    weightOneQSeries N ζ a b τ =
      FormalMultilinearSeries.ofScalarsSum (weightOneIntegralCoeff N ζ a b)
        (Function.Periodic.qParam (N : ℝ) τ : ℂ) := by
  simp [weightOneQSeries, FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul]

/-- Holomorphy of the concrete function needs no modular transformation theorem. -/
theorem mdifferentiable_weightOneQSeries {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) :
    MDiff (weightOneQSeries N ζ a b) := by
  intro τ
  apply UpperHalfPlane.mdifferentiableAt_iff.mpr
  have hd := (analyticAt_weightOneDisc (hζ.norm'_eq_one hN.ne') a b
    (norm_qParam_nat_lt_one hN τ)).differentiableAt.comp (τ : ℂ)
      (Function.Periodic.differentiable_qParam (h := (N : ℝ))).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  exact weightOneQSeries_eq_disc N ζ a b ⟨z, hz⟩

/-- The function has the prescribed constant term as its limit at infinity. -/
theorem tendsto_weightOneQSeries {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) :
    Tendsto (weightOneQSeries N ζ a b) atImInfty
      (𝓝 (weightOneIntegralCoeff N ζ a b 0)) := by
  have h := (analyticAt_weightOneDisc (hζ.norm'_eq_one hN.ne') a b
    (q := 0) (by simp)).continuousAt.tendsto.comp
      (qParam_tendsto_atImInfty (h := (N : ℝ)) (by exact_mod_cast hN))
  simpa only [Function.comp_def, ← weightOneQSeries_eq_disc,
    FormalMultilinearSeries.ofScalarsSum_zero, smul_eq_mul, mul_one] using h

theorem bounded_weightOneQSeries {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) :
    IsBoundedAtImInfty (weightOneQSeries N ζ a b) := by
  exact (tendsto_weightOneQSeries hN hζ a b).isBigO_one ℝ

/-- The width-N period follows directly from the exponential series. -/
theorem periodic_weightOneQSeries {N : ℕ} (hN : 0 < N) (ζ : ℂ) (a b : Fin N) :
    Function.Periodic (weightOneQSeries N ζ a b ∘ ofComplex) (N : ℂ) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hq (z : ℂ) : Function.Periodic.qParam (N : ℝ) (z + N) =
      Function.Periodic.qParam (N : ℝ) z := by
    simp only [Function.Periodic.qParam, Complex.ofReal_natCast]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + N) / N =
      2 * Real.pi * Complex.I * z / N + 2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_periodic _
  intro z
  by_cases! hz : 0 < z.im
  · have hz' : 0 < (z + (N : ℂ)).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz',
      ofComplex_apply_of_im_pos hz, weightOneQSeries, hq]
  · have hz' : (z + (N : ℂ)).im ≤ 0 := by simpa using hz
    simp [ofComplex_apply_of_im_nonpos hz', ofComplex_apply_of_im_nonpos hz]

/-- Even before modularity is proved, the analytic candidate has exactly the
specified Mathlib q-expansion, unconditionally. -/
theorem weightOneQSeries_coeff {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) (n : ℕ) :
    (qExpansion (N : ℝ) (weightOneQSeries N ζ a b)).coeff n =
      weightOneIntegralCoeff N ζ a b n := by
  have hp : Function.Periodic (weightOneQSeries N ζ a b ∘ ofComplex) ((N : ℝ) : ℂ) := by
    rw [Complex.ofReal_natCast]
    exact periodic_weightOneQSeries hN ζ a b
  have hh : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AnalyticAt ℂ (cuspFunction (N : ℝ) (weightOneQSeries N ζ a b)) 0 :=
    analyticAt_cuspFunction_zero hh hp (mdifferentiable_weightOneQSeries hN hζ a b)
      (bounded_weightOneQSeries hN hζ a b)
  let f : ContinuousMap ℍ ℂ :=
    ⟨weightOneQSeries N ζ a b, (mdifferentiable_weightOneQSeries hN hζ a b).continuous⟩
  exact (UpperHalfPlane.qExpansion_coeff_unique (f := f)
      (h := (N : ℝ)) (c := weightOneIntegralCoeff N ζ a b) hh ha
      (hasSum_weightOneQSeries hN hζ a b) n).symm

end VOA.Classification.COne.SSHecke
