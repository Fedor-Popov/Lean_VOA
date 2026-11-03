/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.EisensteinRamanujan
import VOA.Modularity.QDerivProductRule
import VOA.Huang.FrobeniusIndep

/-!
# `q^ν`-series and the Serre derivative, formally and analytically (Anderson–Moore, step 2)

For `ν ∈ ℂ` and a power series `U = Σ uₙ qⁿ` with subexponential coefficients (`U ∈ SubexpPS`,
i.e. convergent on the open unit disc) put

  `amEval ν U z = e^{2πiνz} · Σₙ uₙ e^{2πinz}`   (`Im z > 0`).

This file is the dictionary between the *formal* operations on `(ν, U)` and the analytic ones:

* `hasDerivAt_amEval` — `d/dz amEval ν U = 2πi · amEval ν (ν•U + θU)` (`θ = q d/dq`);
* `amEval_mul` — `amEval 0 A · amEval ν U = amEval ν (A·U)`;
* `serreDerivC_amEval` — the Serre derivative `∂_k` of the library (`serreDerivC`) acts by the
  formal operator `serreF k ν U = ν•U + θU + k•(G₁·U)`, `G₁ = Σ zhuG 1 n qⁿ = −E₂/12`;
* `amSerreIter_amEval` — hence the iterated Serre derivative `ϑ^m = ∂_{2m−2}∘⋯∘∂₀` acts by
  the formal iterate `amSerreF ν m U`;
* `amEval_add_one` (the `T`-eigenvalue `e^{2πiν}`), `tendsto_amEval` (the leading coefficient at
  the cusp), `eq_of_amEval_eq` (uniqueness of `q`-expansions).

All formal operations have coefficients in `ℚ[ν]` applied to the coefficients of `U` (the
Eisenstein coefficients `zhuG 1 n` are rational), which is what the Galois transport of the
Anderson–Moore argument uses.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

open Complex Filter Topology

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-! ## The evaluation map -/

/-- The formal `q`-series of the library (`FormalQSeries = ℂ → ℂ`) attached to `(ν, U)`:
value `uₙ` at the exponent `ν + n`, zero elsewhere. -/
def psQ (ν : ℂ) (U : PowerSeries ℂ) : FormalQSeries := fun e => by
  classical exact if h : ∃ n : ℕ, e = ν + n then PowerSeries.coeff h.choose U else 0

theorem psQ_apply (ν : ℂ) (U : PowerSeries ℂ) (n : ℕ) :
    psQ ν U (ν + n) = PowerSeries.coeff n U := by
  have h : ∃ m : ℕ, ν + (n : ℂ) = ν + m := ⟨n, rfl⟩
  rw [psQ, dif_pos h]
  have hm := h.choose_spec
  have : (h.choose : ℂ) = n := by
    have := hm.symm
    linear_combination this
  rw [Nat.cast_inj.mp this]

/-- `q^ν U`, evaluated at `z` (`q = e^{2πiz}`). -/
def amEval (ν : ℂ) (U : PowerSeries ℂ) (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * ν) *
    ∑' n : ℕ, PowerSeries.coeff n U * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)

theorem amEval_eq_qEvalC (ν : ℂ) (U : PowerSeries ℂ) :
    amEval ν U = qEvalC (psQ ν U) ν := by
  funext z
  rw [amEval, qEvalC, qSeriesC]
  congr 1
  refine tsum_congr fun n => ?_
  rw [qTerm, psQ_apply]

theorem subexp_psQ {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    Subexponential (fun n : ℕ => ‖psQ ν U (ν + (n : ℂ))‖) := by
  have : (fun n : ℕ => ‖psQ ν U (ν + (n : ℂ))‖) = fun n => ‖PowerSeries.coeff n U‖ := by
    funext n; rw [psQ_apply]
  rw [this]; exact hU

/-- Absolute convergence of the bare series on the upper half-plane. -/
theorem summable_norm_coeff_qexp {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) :
    Summable fun n : ℕ =>
      ‖PowerSeries.coeff n U * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ := by
  have hq0 : 0 ≤ ‖qC z‖ := norm_nonneg _
  have hq1 : ‖qC z‖ < 1 := norm_qC_lt_one hz
  have hs := summable_of_subexponential (fun n => norm_nonneg (PowerSeries.coeff n U)) hU hq0 hq1
  refine hs.congr fun n => ?_
  rw [norm_mul, qexp_eq_qC_pow, norm_pow]

/-! ## Derivative -/

/-- The formal `q^ν`-twisted Euler operator: `D(q^ν U) = q^ν (ν U + θ U)`. -/
def thetaNu (ν : ℂ) (U : PowerSeries ℂ) : PowerSeries ℂ := ν • U + theta U

theorem coeff_thetaNu (ν : ℂ) (U : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (thetaNu ν U) = (ν + n) * PowerSeries.coeff n U := by
  rw [thetaNu, map_add, PowerSeries.coeff_smul, theta_coeff, smul_eq_mul]; ring

theorem thetaNu_mem {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) : thetaNu ν U ∈ SubexpPS :=
  SubexpPS.add_mem (SubexpPS.smul_mem hU ν) (theta_mem_subexpPS hU)

/-- **Term-by-term differentiation** of `amEval`. -/
theorem hasDerivAt_amEval {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) :
    HasDerivAt (amEval ν U) (2 * (Real.pi : ℂ) * Complex.I * amEval ν (thetaNu ν U) z) z := by
  have hz0 : (0 : ℝ) < z.im := hz
  have hc : (0 : ℝ) < z.im / 2 := by linarith
  have hzc : z ∈ imGT (z.im / 2) := by change z.im / 2 < z.im; linarith
  have h := hasDerivAt_qEvalC (psQ ν U) ν (subexp_psQ hU) hc hzc
  rw [← amEval_eq_qEvalC] at h
  convert h using 2
  rw [amEval_eq_qEvalC, qEvalC, qEvalC, qSeriesC, qSeriesC]
  congr 1
  refine tsum_congr fun n => ?_
  rw [qTerm, qTerm, psQ_apply, qDeriv, psQ_apply, coeff_thetaNu]

theorem differentiableOn_amEval {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    DifferentiableOn ℂ (amEval ν U) (imGT 0) := fun _ hz =>
  (hasDerivAt_amEval hU hz).differentiableAt.differentiableWithinAt

theorem differentiableAt_amEval {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) : DifferentiableAt ℂ (amEval ν U) z :=
  (hasDerivAt_amEval hU hz).differentiableAt

theorem analyticAt_amEval {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) : AnalyticAt ℂ (amEval ν U) z :=
  (differentiableOn_amEval hU).analyticAt ((isOpen_imGT 0).mem_nhds hz)

/-! ## Products -/

theorem amEval_zero_left (A : PowerSeries ℂ) (z : ℂ) :
    amEval 0 A z = ∑' n : ℕ,
      PowerSeries.coeff n A * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) := by
  rw [amEval, mul_zero, Complex.exp_zero, one_mul]

/-- **Products**: `amEval 0 A · amEval ν U = amEval ν (A·U)`. -/
theorem amEval_mul {A U : PowerSeries ℂ} (hA : A ∈ SubexpPS) (hU : U ∈ SubexpPS) (ν : ℂ)
    {z : ℂ} (hz : z ∈ imGT 0) :
    amEval 0 A z * amEval ν U z = amEval ν (A * U) z := by
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_norm_coeff_qexp hA hz) (summable_norm_coeff_qexp hU hz)
  rw [amEval_zero_left, amEval, amEval, mul_left_comm, hcauchy]
  congr 1
  refine tsum_congr fun m => ?_
  rw [VOA.coeff_mul_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [qexp_eq_qC_pow, qexp_eq_qC_pow, qexp_eq_qC_pow,
    show m = n + (m - n) from by omega, pow_add]
  simp only [show n + (m - n) - n = m - n from by omega]
  ring

/-! ## The Serre derivative -/

/-- `G₁ = Σ zhuG 1 n qⁿ` (`= −E₂/12`). -/
def G1ser : PowerSeries ℂ := PowerSeries.mk (zhuG 1)

theorem G1ser_mem : G1ser ∈ SubexpPS := mk_zhuG_mem_subexpPS 1

theorem amEval_G1ser {z : ℂ} (hz : z ∈ imGT 0) :
    amEval 0 G1ser z = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * G2C z := by
  rw [← zhuGC_one hz, amEval_zero_left, zhuGC]
  refine tsum_congr fun n => ?_
  rw [G1ser, PowerSeries.coeff_mk]

/-- The formal Serre derivative of weight `k`. -/
def serreF (k : ℤ) (ν : ℂ) (U : PowerSeries ℂ) : PowerSeries ℂ :=
  thetaNu ν U + (k : ℂ) • (G1ser * U)

theorem serreF_mem {k : ℤ} {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    serreF k ν U ∈ SubexpPS :=
  SubexpPS.add_mem (thetaNu_mem hU) (SubexpPS.smul_mem (SubexpPS.mul_mem G1ser_mem hU) _)

theorem amEval_add {ν : ℂ} {U V : PowerSeries ℂ} (hU : U ∈ SubexpPS) (hV : V ∈ SubexpPS)
    {z : ℂ} (hz : z ∈ imGT 0) : amEval ν (U + V) z = amEval ν U z + amEval ν V z := by
  have h1 : Summable fun n : ℕ => PowerSeries.coeff n U *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) :=
    (summable_norm_coeff_qexp hU hz).of_norm
  have h2 : Summable fun n : ℕ => PowerSeries.coeff n V *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) :=
    (summable_norm_coeff_qexp hV hz).of_norm
  rw [amEval, amEval, amEval, ← mul_add, ← h1.tsum_add h2]
  congr 1
  refine tsum_congr fun n => ?_
  rw [map_add]; ring

theorem amEval_smul (c ν : ℂ) (U : PowerSeries ℂ) (z : ℂ) :
    amEval ν (c • U) z = c * amEval ν U z := by
  simp only [amEval, PowerSeries.coeff_smul, smul_eq_mul, mul_assoc, tsum_mul_left]
  ring

theorem amEval_sub {ν : ℂ} {U V : PowerSeries ℂ} (hU : U ∈ SubexpPS) (hV : V ∈ SubexpPS)
    {z : ℂ} (hz : z ∈ imGT 0) : amEval ν (U - V) z = amEval ν U z - amEval ν V z := by
  have h := amEval_add hU (SubexpPS.smul_mem hV (-1 : ℂ)) (ν := ν) hz
  rw [amEval_smul] at h
  rw [sub_eq_add_neg, show -V = (-1 : ℂ) • V from by simp, h]; ring

/-- **The Serre derivative acts formally.** -/
theorem serreDerivC_amEval (k : ℤ) {ν : ℂ} {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) :
    serreDerivC k (amEval ν U) z = amEval ν (serreF k ν U) z := by
  rw [serreDerivC, (hasDerivAt_amEval hU hz).deriv, serreF,
    amEval_add (thetaNu_mem hU) (SubexpPS.smul_mem (SubexpPS.mul_mem G1ser_mem hU) _) hz,
    amEval_smul, ← amEval_mul G1ser_mem hU ν hz, amEval_G1ser hz]
  have := two_pi_I_ne_zero
  field_simp

/-! ## Iterated Serre derivatives -/

/-- The iterated Serre derivative `ϑ^m = ∂_{2m−2} ∘ ⋯ ∘ ∂₂ ∘ ∂₀` (weight `0` input). -/
def amSerreIter : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, f => f
  | m + 1, f => serreDerivC (2 * (m : ℤ)) (amSerreIter m f)

@[simp] theorem amSerreIter_zero (f : ℂ → ℂ) : amSerreIter 0 f = f := rfl

theorem amSerreIter_succ (m : ℕ) (f : ℂ → ℂ) :
    amSerreIter (m + 1) f = serreDerivC (2 * (m : ℤ)) (amSerreIter m f) := rfl

/-- The formal iterate. -/
def amSerreF (ν : ℂ) : ℕ → PowerSeries ℂ → PowerSeries ℂ
  | 0, U => U
  | m + 1, U => serreF (2 * (m : ℤ)) ν (amSerreF ν m U)

@[simp] theorem amSerreF_zero (ν : ℂ) (U : PowerSeries ℂ) : amSerreF ν 0 U = U := rfl

theorem amSerreF_succ (ν : ℂ) (m : ℕ) (U : PowerSeries ℂ) :
    amSerreF ν (m + 1) U = serreF (2 * (m : ℤ)) ν (amSerreF ν m U) := rfl

theorem amSerreF_mem (ν : ℂ) (m : ℕ) {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    amSerreF ν m U ∈ SubexpPS := by
  induction m with
  | zero => exact hU
  | succ m ih => exact serreF_mem ih

/-- **The iterated Serre derivative acts formally**, on the whole upper half-plane. -/
theorem amSerreIter_amEval (ν : ℂ) (m : ℕ) {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) {z : ℂ}
    (hz : z ∈ imGT 0) :
    amSerreIter m (amEval ν U) z = amEval ν (amSerreF ν m U) z := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    rw [amSerreIter_succ, amSerreF_succ]
    have hev : amSerreIter m (amEval ν U) =ᶠ[𝓝 z] amEval ν (amSerreF ν m U) := by
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
      exact ih hw
    rw [serreDerivC_congr_of_eventuallyEq _ hev, serreDerivC_amEval _ (amSerreF_mem ν m hU) hz]

/-! ## The `T`-eigenvalue -/

theorem amEval_add_one (ν : ℂ) (U : PowerSeries ℂ) (z : ℂ) :
    amEval ν U (z + 1) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ν) * amEval ν U z := by
  rw [amEval, amEval]
  have hT : ∀ n : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z + 1))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z) := by
    intro n
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z + 1)
        = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        from by ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp_rw [hT]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (z + 1) * ν
      = 2 * (Real.pi : ℂ) * Complex.I * z * ν + 2 * (Real.pi : ℂ) * Complex.I * ν from by ring,
    Complex.exp_add]
  ring

/-! ## The cusp: leading coefficient and uniqueness -/

theorem qexp_I_mul (n : ℕ) (y : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (Complex.I * y))
      = ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ) ^ n := by
  rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (Complex.I * y)
      = 2 * (Real.pi : ℂ) * (n : ℂ) * y * (Complex.I * Complex.I) from by ring, Complex.I_mul_I]
  ring

theorem I_mul_mem_imGT {y : ℝ} (hy : 0 < y) : Complex.I * (y : ℂ) ∈ imGT 0 := by
  change (0 : ℝ) < (Complex.I * (y : ℂ)).im
  simpa using hy

/-- The bare series along the imaginary axis is a real-variable power series in
`t = e^{−2πy}`. -/
theorem amEval_zero_I_mul (U : PowerSeries ℂ) (y : ℝ) :
    amEval 0 U (Complex.I * y)
      = ∑' n : ℕ, PowerSeries.coeff n U * ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ) ^ n := by
  rw [amEval_zero_left]
  exact tsum_congr fun n => by rw [qexp_I_mul]

/-- A convergent power series tends to its constant term as `t → 0⁺` (quantitative form). -/
theorem norm_tsum_sub_coeff_zero_le {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      ‖(∑' n : ℕ, PowerSeries.coeff n U * (t : ℂ) ^ n) - PowerSeries.coeff 0 U‖ ≤ C * t := by
  have hsh : Subexponential fun m => ‖PowerSeries.coeff (m + 1) U‖ := hU.shift 1
  set C : ℝ := ∑' m, ‖PowerSeries.coeff (m + 1) U‖ * (1 / 2 : ℝ) ^ m with hC
  have hCs : Summable fun m => ‖PowerSeries.coeff (m + 1) U‖ * (1 / 2 : ℝ) ^ m :=
    summable_of_subexponential (fun _ => norm_nonneg _) hsh (by norm_num) (by norm_num)
  refine ⟨C, fun t ht0 ht1 => ?_⟩
  have ht1' : t < 1 := by linarith
  have hsum : Summable fun n => PowerSeries.coeff n U * (t : ℂ) ^ n := by
    refine Summable.of_norm ?_
    have := summable_of_subexponential (fun _ => norm_nonneg _) hU ht0 ht1'
    refine this.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
  have hsplit := hsum.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, pow_zero, mul_one] at hsplit
  rw [← hsplit, add_sub_cancel_left]
  have htail : ∑' m, PowerSeries.coeff (m + 1) U * (t : ℂ) ^ (m + 1)
      = (t : ℂ) * ∑' m, PowerSeries.coeff (m + 1) U * (t : ℂ) ^ m := by
    rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
  rw [htail, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, mul_comm C t]
  refine mul_le_mul_of_nonneg_left ?_ ht0
  have hs1 : Summable fun m => ‖PowerSeries.coeff (m + 1) U * (t : ℂ) ^ m‖ := by
    have := summable_of_subexponential (fun _ => norm_nonneg _) hsh ht0 ht1'
    refine this.congr fun m => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
  refine le_trans (norm_tsum_le_tsum_norm hs1) (hs1.tsum_le_tsum (fun m => ?_) hCs)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0]
  gcongr

/-- **The leading coefficient at the cusp**: along `z = iy`, `y → ∞`, the bare series tends to
its constant term. -/
theorem tendsto_amEval_zero {U : PowerSeries ℂ} (hU : U ∈ SubexpPS) :
    Tendsto (fun y : ℝ => amEval 0 U (Complex.I * y)) atTop (𝓝 (PowerSeries.coeff 0 U)) := by
  obtain ⟨C, hC⟩ := norm_tsum_sub_coeff_zero_le hU
  have ht : Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    refine tendsto_neg_atTop_atBot.comp ?_
    exact Tendsto.const_mul_atTop (by positivity) tendsto_id
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hCt : Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    simpa using ht.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hCt
  have hev : ∀ᶠ y : ℝ in atTop, Real.exp (-(2 * Real.pi * y)) ≤ 1 / 2 :=
    (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [hev] with y hy
  rw [amEval_zero_I_mul]
  exact hC _ (Real.exp_pos _).le hy

/-- **Uniqueness of `q`-expansions**: a convergent power series whose evaluation vanishes on
the imaginary axis is zero. -/
theorem eq_zero_of_amEval_zero {U : PowerSeries ℂ} (hU : U ∈ SubexpPS)
    (h : ∀ y : ℝ, 0 < y → amEval 0 U (Complex.I * y) = 0) : U = 0 := by
  have hc := VOA.Huang.FrobeniusLog.eq_zero_of_tsum_pow_eq_zero
    (a := fun n => PowerSeries.coeff n U) hU
    (fun t ht0 ht1 => by
      have hy : 0 < -Real.log t / (2 * Real.pi) := by
        have := Real.log_neg ht0 ht1
        have := Real.pi_pos
        exact div_pos (by linarith) (by positivity)
      have h1 := h _ hy
      rw [amEval_zero_I_mul] at h1
      have he : Real.exp (-(2 * Real.pi * (-Real.log t / (2 * Real.pi)))) = t := by
        rw [show -(2 * Real.pi * (-Real.log t / (2 * Real.pi))) = Real.log t from by
          field_simp, Real.exp_log ht0]
      rwa [he] at h1)
  ext n
  simpa using hc n

/-- Uniqueness, in the form used for comparing two `q^ν`-series. -/
theorem eq_of_amEval_eq {ν : ℂ} {U V : PowerSeries ℂ} (hU : U ∈ SubexpPS) (hV : V ∈ SubexpPS)
    (h : ∀ z ∈ imGT 0, amEval ν U z = amEval ν V z) : U = V := by
  have hUV : U - V ∈ SubexpPS := SubexpPS.sub_mem hU hV
  refine sub_eq_zero.mp (eq_zero_of_amEval_zero hUV fun y hy => ?_)
  have hz := I_mul_mem_imGT hy
  have h1 := h _ hz
  have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * y) * ν) ≠ 0 :=
    Complex.exp_ne_zero _
  have h2 : amEval ν (U - V) (Complex.I * y) = 0 := by
    rw [amEval_sub hU hV hz, h1, sub_self]
  rw [amEval] at h2
  rw [amEval_zero_left]
  exact (mul_eq_zero.mp h2).resolve_left hne

end VOA.Huang.AndersonMoore
