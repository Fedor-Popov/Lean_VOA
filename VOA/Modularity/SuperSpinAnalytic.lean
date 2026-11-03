/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinRelations
import VOA.Modularity.EisensteinAnalytic
import VOA.Modularity.OnePointDescent
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Analytic evaluation of the four formal spin-sector coefficient series

This file evaluates the coordinate-normalized formal series `spinQ p k` on the upper
half-plane.  Its exponents are `N/2`, so the analytic function is

`sum_N spinQ p k (N/2) exp(2*pi*i*tau*N/2)`.

Equivalently, pull the coefficients back to an ordinary power series in the doubled index `N`
and evaluate that power series at `tau/2`.  This observation lets us reuse the repository's
`qEvalC` convergence and holomorphy layer without pretending that a half-lattice is an integral
lattice.

The estimates below prove absolute convergence and uniform convergence on every closed
sub-half-plane.  The elementary `T^2` law follows term by term.  No `S` law is asserted: the
current repository and Mathlib do not contain the required primary theta/Lambert transformation
(equivalently, its Poisson-summation input) for all four characteristics.

Normalization is exact: `spinQ = (2*pi*i)^(-k-1) spinP`.  Thus the `(++ )`, odd-index family is
literally `zhuG`; in particular `k=1` is the visible quasimodular `G2` anomaly, while `k>=3` odd
uses the existing analytic Eisenstein theorem.
-/

namespace VOA

open Complex
open scoped BigOperators

set_option autoImplicit false

/-! ## Pullback from the half-lattice -/

/-- The coefficient series indexed by the doubled exponent: its `N`-th coefficient is the
coefficient of `q^(N/2)` in `spinQ p k`. -/
noncomputable def spinQIndexSeries (p : SpinPair) (k : Nat) : FormalQSeries :=
  fun e => spinQ p k (e / 2)

@[simp] theorem spinQIndexSeries_nat (p : SpinPair) (k N : Nat) :
    spinQIndexSeries p k (N : Complex) = spinQ p k (halfQExponent N) := by
  rfl

/-- The `N`-th analytic half-lattice term. -/
noncomputable def spinQAnalyticTerm (p : SpinPair) (k N : Nat) (z : Complex) : Complex :=
  spinQ p k (halfQExponent N) *
    Complex.exp (spinTwoPiI * z * halfQExponent N)

/-- Analytic evaluation of the normalized spin coefficient on the half-lattice. -/
noncomputable def spinQAnalytic (p : SpinPair) (k : Nat) (z : Complex) : Complex :=
  ∑' N : Nat, spinQAnalyticTerm p k N z

/-! ## Polynomial coefficient bound -/

@[simp] theorem norm_spinPhase_value (a : SpinPhase) : ‖SpinPhase.value a‖ = 1 := by
  by_cases h : a = SpinPhase.plus <;> simp [SpinPhase.value, h]

theorem norm_spinPhase_value_pow (a : SpinPhase) (n : Nat) :
    ‖SpinPhase.value a ^ n‖ = 1 := by simp

theorem norm_spinPhase_value_inv_pow (a : SpinPhase) (n : Nat) :
    ‖(SpinPhase.value a)⁻¹ ^ n‖ = 1 := by simp

/-- A single signed integral Lambert summand is bounded by twice its unsigned monomial. -/
theorem norm_spinIntegralSummand_le (lambda : SpinPhase) (k : Nat) (p : Nat × Nat) :
    ‖(p.1 : Complex) ^ k * SpinPhase.value lambda ^ p.2 -
        (-(p.1 : Complex)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2‖
      ≤ 2 * (p.1 : Real) ^ k := by
  calc
    ‖(p.1 : Complex) ^ k * SpinPhase.value lambda ^ p.2 -
        (-(p.1 : Complex)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2‖
      ≤ ‖(p.1 : Complex) ^ k * SpinPhase.value lambda ^ p.2‖ +
          ‖(-(p.1 : Complex)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2‖ := norm_sub_le _ _
    _ = 2 * (p.1 : Real) ^ k := by
      simp [norm_pow]
      ring

/-- A single half-integral Lambert summand is bounded by the same crude integral monomial.
The discarded factor `2^(-k)` only improves the estimate. -/
theorem norm_spinHalfSummand_le (lambda : SpinPhase) (k : Nat) (p : Nat × Nat) :
    ‖if Odd p.1 then
        ((p.1 : Complex) / 2) ^ k * SpinPhase.value lambda ^ p.2 -
          (-((p.1 : Complex) / 2)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2
      else 0‖ ≤ 2 * (p.1 : Real) ^ k := by
  split_ifs
  · calc
      ‖((p.1 : Complex) / 2) ^ k * SpinPhase.value lambda ^ p.2 -
          (-((p.1 : Complex) / 2)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2‖
        ≤ ‖((p.1 : Complex) / 2) ^ k * SpinPhase.value lambda ^ p.2‖ +
            ‖(-((p.1 : Complex) / 2)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2‖ :=
          norm_sub_le _ _
      _ = 2 * ((p.1 : Real) / 2) ^ k := by
        simp [norm_pow]
        ring
      _ ≤ 2 * (p.1 : Real) ^ k := by
        gcongr
        exact div_le_self (Nat.cast_nonneg p.1) (by norm_num)
  · simp

theorem norm_spinIntegralTail_le (lambda : SpinPhase) (k n : Nat) :
    ‖spinIntegralTail lambda k n‖ ≤ 2 * (n : Real) ^ (k + 1) := by
  rw [spinIntegralTail]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        ((p.1 : Complex) ^ k * SpinPhase.value lambda ^ p.2 -
          (-(p.1 : Complex)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2)‖
      ≤ ∑ p ∈ n.divisorsAntidiagonal, 2 * (p.1 : Real) ^ k := by
        exact norm_sum_le_of_le _ fun p hp => norm_spinIntegralSummand_le lambda k p
    _ = 2 * (ArithmeticFunction.sigma k n : Nat) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Nat.sum_divisorsAntidiagonal (fun m _ => (m : Real) ^ k),
        ArithmeticFunction.sigma_apply]
      push_cast
      rfl
    _ ≤ 2 * (n : Real) ^ (k + 1) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n) (by norm_num)

theorem norm_spinHalfTail_le (lambda : SpinPhase) (k N : Nat) :
    ‖spinHalfTail lambda k N‖ ≤ 2 * (N : Real) ^ (k + 1) := by
  rw [spinHalfTail]
  calc
    ‖∑ p ∈ N.divisorsAntidiagonal, if Odd p.1 then
        ((p.1 : Complex) / 2) ^ k * SpinPhase.value lambda ^ p.2 -
          (-((p.1 : Complex) / 2)) ^ k * (SpinPhase.value lambda)⁻¹ ^ p.2 else 0‖
      ≤ ∑ p ∈ N.divisorsAntidiagonal, 2 * (p.1 : Real) ^ k := by
        exact norm_sum_le_of_le _ fun p hp => norm_spinHalfSummand_le lambda k p
    _ = 2 * (ArithmeticFunction.sigma k N : Nat) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Nat.sum_divisorsAntidiagonal (fun m _ => (m : Real) ^ k),
        ArithmeticFunction.sigma_apply]
      push_cast
      rfl
    _ ≤ 2 * (N : Real) ^ (k + 1) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k N) (by norm_num)

/-- Uniform polynomial growth of the doubled-index coefficients. -/
theorem norm_spinQIndexSeries_le (p : SpinPair) (k N : Nat) :
    ‖spinQIndexSeries p k (N : Complex)‖ ≤
      ‖spinQ p k 0‖ +
        (2 * ‖(spinTwoPiI ^ (k + 1))⁻¹ *
          (spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex))‖) *
            (N : Real) ^ (k + 1) := by
  by_cases hN : N = 0
  · subst N
    simpa [spinQIndexSeries, halfQExponent]
  · rw [spinQIndexSeries_nat, spinQ_apply, spinP_coeff_half, spinPNatCoeff,
      if_neg hN, norm_mul]
    by_cases hmu : p.mu = SpinPhase.plus
    · rw [if_pos hmu]
      by_cases he : Even N
      · rw [if_pos he, norm_mul]
        have htail := norm_spinIntegralTail_le p.lambda k (N / 2)
        have hdiv : ((N / 2 : Nat) : Real) ^ (k + 1) ≤ (N : Real) ^ (k + 1) := by
          gcongr
          exact_mod_cast Nat.div_le_self N 2
        calc
          ‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
              (‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖ *
                ‖spinIntegralTail p.lambda k (N / 2)‖)
            ≤ ‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
                (‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖ *
                  (2 * (N : Real) ^ (k + 1))) := by
                    gcongr
                    exact htail.trans
                      (mul_le_mul_of_nonneg_left hdiv (by norm_num))
          _ ≤ ‖spinQ p k 0‖ +
              (2 * ‖(spinTwoPiI ^ (k + 1))⁻¹ *
                (spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex))‖) *
                  (N : Real) ^ (k + 1) := by
              rw [norm_mul]
              have hnon : 0 ≤ 2 *
                  (‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
                    ‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖) *
                      (N : Real) ^ (k + 1) := by positivity
              nlinarith [norm_nonneg (spinQ p k 0)]
      · rw [if_neg he, mul_zero, norm_zero]
        rw [mul_zero]
        positivity
    · rw [if_neg hmu, norm_mul]
      have htail := norm_spinHalfTail_le p.lambda k N
      calc
        ‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
            (‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖ *
              ‖spinHalfTail p.lambda k N‖)
          ≤ ‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
              (‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖ *
                (2 * (N : Real) ^ (k + 1))) := by
                  gcongr
        _ ≤ ‖spinQ p k 0‖ +
            (2 * ‖(spinTwoPiI ^ (k + 1))⁻¹ *
              (spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex))‖) *
                (N : Real) ^ (k + 1) := by
            rw [norm_mul]
            have hnon : 0 ≤ 2 *
                (‖(spinTwoPiI ^ (k + 1))⁻¹‖ *
                  ‖spinTwoPiI ^ (k + 1) / (Nat.factorial k : Complex)‖) *
                    (N : Real) ^ (k + 1) := by positivity
            nlinarith [norm_nonneg (spinQ p k 0)]

theorem subexponential_spinQIndexSeries (p : SpinPair) (k : Nat) :
    Subexponential (fun N : Nat => ‖spinQIndexSeries p k (N : Complex)‖) := by
  refine Subexponential.of_le (norm_spinQIndexSeries_le p k) ?_
  exact (subexponential_const _).add
    ((subexponential_pow (k + 1)).const_mul (by positivity))

/-! ## Absolute and locally uniform convergence -/

theorem summable_norm_spinQAnalyticTerm (p : SpinPair) (k : Nat) {z : Complex}
    (hz : z ∈ imGT 0) :
    Summable (fun N : Nat => ‖spinQAnalyticTerm p k N z‖) := by
  have hzhalf : z / 2 ∈ imGT 0 := by
    show 0 < (z / 2).im
    simpa using div_pos hz (by norm_num : (0 : Real) < 2)
  refine (summable_of_subexponential (fun N => norm_nonneg _)
    (subexponential_spinQIndexSeries p k)
    (norm_nonneg (qC (z / 2))) (norm_qC_lt_one hzhalf)).congr (fun N => ?_)
  rw [spinQAnalyticTerm, ← spinQIndexSeries_nat, norm_mul]
  congr 1
  have hexp : Complex.exp (spinTwoPiI * z * halfQExponent N) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * (N : Complex) * (z / 2)) := by
    congr 1
    simp [spinTwoPiI, halfQExponent]
    ring
  rw [hexp, qexp_eq_qC_pow, norm_pow]

theorem summable_spinQAnalyticTerm (p : SpinPair) (k : Nat) {z : Complex}
    (hz : z ∈ imGT 0) : Summable (spinQAnalyticTerm p k · z) :=
  Summable.of_norm (summable_norm_spinQAnalyticTerm p k hz)

theorem spinQAnalytic_eq_qEvalC (p : SpinPair) (k : Nat) (z : Complex) :
    spinQAnalytic p k z = qEvalC (spinQIndexSeries p k) 0 (z / 2) := by
  rw [spinQAnalytic, qEvalC, qSeriesC]
  simp only [mul_zero, Complex.exp_zero, one_mul]
  refine tsum_congr fun N => ?_
  rw [spinQAnalyticTerm, qTerm]
  simp only [zero_add]
  rw [spinQIndexSeries_nat]
  congr 1
  simp [halfQExponent, spinTwoPiI]
  ring

/-- Uniform convergence on every closed sub-half-plane `Im z >= c`, `c>0`. -/
theorem tendstoUniformlyOn_spinQAnalytic (p : SpinPair) (k : Nat) {c : Real} (hc : 0 < c) :
    TendstoUniformlyOn
      (fun M z => ∑ N ∈ Finset.range M, spinQAnalyticTerm p k N z)
      (spinQAnalytic p k) Filter.atTop {z : Complex | c ≤ z.im} := by
  let r : Real := Real.exp (-(Real.pi * c))
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  obtain ⟨C, hC⟩ := subexponential_spinQIndexSeries p k (qAux r)
    (one_lt_qAux hrpos hr1)
  have hsr0 : 0 ≤ qAux r * r := (qAux_mul_pos hrpos hr1).le
  have hsr1 : qAux r * r < 1 := qAux_mul_lt_one hrpos hr1
  have hmajor : Summable (fun N : Nat => C * (qAux r * r) ^ N) :=
    (summable_geometric_of_lt_one hsr0 hsr1).mul_left C
  refine tendstoUniformlyOn_tsum_nat hmajor ?_
  intro N z hz
  rw [spinQAnalyticTerm, norm_mul, Complex.norm_exp]
  have hexp : (spinTwoPiI * z * halfQExponent N).re = -(Real.pi * N * z.im) := by
    simp [spinTwoPiI, halfQExponent, Complex.mul_re, Complex.mul_im]
    ring
  rw [hexp]
  have hq : Real.exp (-(Real.pi * N * z.im)) ≤ r ^ N := by
    change Real.exp (-(Real.pi * N * z.im)) ≤
      Real.exp (-(Real.pi * c)) ^ N
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hnon : 0 ≤ Real.pi * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hz hnon]
  have hcoef := hC N
  have hC0 : 0 ≤ C := by
    have := hC 0
    simpa using le_trans (norm_nonneg _) this
  calc
    ‖spinQ p k (halfQExponent N)‖ * Real.exp (-(Real.pi * N * z.im))
      ≤ (C * qAux r ^ N) * r ^ N :=
        mul_le_mul hcoef hq (Real.exp_pos _).le
          (mul_nonneg hC0 (pow_nonneg (lt_trans zero_lt_one (one_lt_qAux hrpos hr1)).le N))
    _ = C * (qAux r * r) ^ N := by rw [mul_pow]; ring

theorem differentiableOn_spinQAnalytic (p : SpinPair) (k : Nat) :
    DifferentiableOn Complex (spinQAnalytic p k) (imGT 0) := by
  have heq : spinQAnalytic p k =
      fun z => qEvalC (spinQIndexSeries p k) 0 (z / 2) := by
    funext z
    exact spinQAnalytic_eq_qEvalC p k z
  rw [heq]
  intro z hz
  have hzhalf : z / 2 ∈ imGT 0 := by
    show 0 < (z / 2).im
    simpa using div_pos hz (by norm_num : (0 : Real) < 2)
  have hsub : Subexponential
      (fun n : Nat => ‖spinQIndexSeries p k (0 + (n : Complex))‖) := by
    simpa using subexponential_spinQIndexSeries p k
  have houter := differentiableOn_qEvalC (spinQIndexSeries p k) 0 hsub
  have hinner : DifferentiableWithinAt Complex (fun w : Complex => w / 2) (imGT 0) z :=
    ((differentiableAt_id : DifferentiableAt Complex (fun w : Complex => w) z).div_const
      (2 : Complex)).differentiableWithinAt
  have hmaps : Set.MapsTo (fun w : Complex => w / 2) (imGT 0) (imGT 0) := by
    intro w hw
    show 0 < (w / 2).im
    simpa using div_pos hw (by norm_num : (0 : Real) < 2)
  simpa [Function.comp_apply] using (houter (z / 2) hzhalf).comp z hinner hmaps

/-! ## Agreement with fractional `q`-evaluation and the `T^2` law -/

theorem spinQAnalytic_coe_eq_qEvalAtFrac (p : SpinPair) (k : Nat) (tau : UpperHalfPlane) :
    spinQAnalytic p k (tau : Complex) = qEvalAtFrac (spinQ p k) 0 2 tau := by
  rw [spinQAnalytic, qEvalAtFrac]
  simp only [mul_zero, Complex.exp_zero, one_mul]
  refine tsum_congr fun N => ?_
  rw [spinQAnalyticTerm]
  congr 1
  simp [halfQExponent, spinTwoPiI]

/-- Elementary theta-group translation: every half-integral exponent is fixed by `tau -> tau+2`. -/
theorem spinQAnalytic_add_two (p : SpinPair) (k : Nat) (z : Complex) :
    spinQAnalytic p k (z + 2) = spinQAnalytic p k z := by
  rw [spinQAnalytic, spinQAnalytic]
  refine tsum_congr fun N => ?_
  rw [spinQAnalyticTerm, spinQAnalyticTerm]
  congr 1
  rw [show spinTwoPiI * (z + 2) * halfQExponent N =
      spinTwoPiI * z * halfQExponent N + (N : Complex) * (2 * Real.pi * Complex.I) by
        simp [spinTwoPiI, halfQExponent]
        ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-! ## The invariant-sector coefficient cells and the visible anomaly -/

/-- The exceptional invariant `k=0` series is the constant `-1/2` after coordinate
normalization.  It does not obey a weight-one transformation law. -/
theorem spinQAnalytic_pp_zero_coeff (N : Nat) :
    spinQ SpinPair.pp 0 (halfQExponent N) = if N = 0 then -(1 / 2 : Complex) else 0 := by
  by_cases hN : N = 0
  · subst N
    rw [if_pos rfl, show halfQExponent 0 = 0 by simp [halfQExponent], spinQ_cusp]
    simp [spinQCusp, spinPCusp_pp_zero, spinTwoPiI]
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [Complex.I_sq]
  · rw [if_neg hN, spinQ_apply, spinP_coeff_half, spinPNatCoeff, if_neg hN]
    simp only [SpinPair.pp, if_true]
    split_ifs
    · rw [spinIntegralTail]
      simp [SpinPhase.value_plus]
    · simp

theorem spinQAnalytic_pp_zero (z : Complex) :
    spinQAnalytic SpinPair.pp 0 z = -(1 / 2 : Complex) := by
  rw [spinQAnalytic, tsum_eq_single 0]
  · rw [spinQAnalyticTerm, spinQAnalytic_pp_zero_coeff]
    simp [halfQExponent]
  · intro N hN
    rw [spinQAnalyticTerm, spinQAnalytic_pp_zero_coeff, if_neg hN, zero_mul]

/-- At `k=1`, every integral coefficient of the invariant sector is the repository's `G2`
coefficient.  Its analytic transformation remains the already-proved quasimodular `G2C` law;
the only omitted step here is the elementary even-index reindexing of the half-lattice sum. -/
theorem spinQAnalytic_pp_one_coeff (n : Nat) :
    spinQ SpinPair.pp 1 (n : Complex) = zhuG 1 n :=
  spinQ_pp_odd_eq_zhuG (j := 1) (by norm_num) n

/-- For `j>=2`, the invariant odd-index coefficients are exactly the higher Zhu--Eisenstein
coefficients.  The three other characteristics require a primary theta/Lambert `S` identity. -/
theorem spinQAnalytic_pp_higher_coeff {j : Nat} (hj : 2 ≤ j) (n : Nat) :
    spinQ SpinPair.pp (2 * j - 1) (n : Complex) = zhuG j n :=
  spinQ_pp_odd_eq_zhuG (by omega) n

end VOA
