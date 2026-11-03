import VOA.Huang.GenusOneIntCoordSubstitution
import Mathlib.Analysis.Analytic.Binomial

/-!
# Absolutely convergent evaluation of the bracket-coordinate power series

Step (5c) of the proof of (G1). The explicit formal bracket coefficients
of `GenusOneIntCoordSubstitution` (`bracketCoeff α n r`, the coefficients of
`e^{αz} ((e^z − 1)/z)^{−n−r−1}`) are identified with Taylor coefficients of honest analytic
functions, with a majorant that is GEOMETRIC in the integer part of the exponent. This is the
scalar input of the Laurent expansion of the genus-one iterate in the torus coordinate
(`GenusOneG1eLaurent`), which needs NO square-trace-mass bound.

* `PSConv P ρ`, `psMass P ρ`, `psEval P u` — absolute convergence, majorant mass, evaluation;
* `conv_mul`, `psEval_mul`, `conv_pow`, `psEval_pow` — Cauchy products;
* `conv_expA`, `psEval_expA` — `e^{αu}`; `conv_unit`, `psEval_unit` — `E(u) = (e^u − 1)/u`;
* `psEval_unitPower` — `Σ_r [z^r]E^b u^r = E(u)^b` (principal power) for `‖u‖ ≤ 1/3`,
  via the analytic binomial series and Fubini;
* `unitPower_add_nat` — `E^{b+m} = E^b E^m` formally;
* `bracketFactor` — the series `e^{αz} E^{c'} E^m` with
  `bracketCoeff α n r = [z^r] bracketFactor α c' m` when `−n−r−1 = c' + m`, its evaluation and
  the bound `psMass ≤ e^{‖α‖ρ} · psMass(E^{c'}) · (psMass E)^m`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open Complex
open VOA.Huang.GenusOne.IntCoord (exponentialUnit exponentialUnitPower bracketCoeff
  exponentialUnit_sub_one_constant exponentialUnitPower_coeff)
open scoped BigOperators

/-! ## §1 Evaluation and majorants -/

/-- `P` converges absolutely at radius `ρ`. -/
def PSConv (P : PowerSeries ℂ) (ρ : ℝ) : Prop :=
  Summable (fun r : ℕ => ‖PowerSeries.coeff r P‖ * ρ ^ r)

/-- The majorant mass of `P` at radius `ρ`. -/
def psMass (P : PowerSeries ℂ) (ρ : ℝ) : ℝ := ∑' r : ℕ, ‖PowerSeries.coeff r P‖ * ρ ^ r

/-- The evaluation of `P` at `u`. -/
def psEval (P : PowerSeries ℂ) (u : ℂ) : ℂ := ∑' r : ℕ, PowerSeries.coeff r P * u ^ r

theorem psMass_nonneg (P : PowerSeries ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ psMass P ρ :=
  tsum_nonneg fun r => mul_nonneg (norm_nonneg _) (pow_nonneg hρ r)

theorem summable_norm_of_conv {P : PowerSeries ℂ} {ρ : ℝ} (h : PSConv P ρ) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) : Summable (fun r => ‖PowerSeries.coeff r P * u ^ r‖) := by
  refine h.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu r) (norm_nonneg _)

theorem hasSum_psEval {P : PowerSeries ℂ} {ρ : ℝ} (h : PSConv P ρ) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    HasSum (fun r => PowerSeries.coeff r P * u ^ r) (psEval P u) :=
  (summable_norm_of_conv h hu).of_norm.hasSum

theorem tsum_norm_le_psMass {P : PowerSeries ℂ} {ρ : ℝ} (h : PSConv P ρ) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) : ∑' r, ‖PowerSeries.coeff r P * u ^ r‖ ≤ psMass P ρ := by
  refine Summable.tsum_le_tsum (fun r => ?_) (summable_norm_of_conv h hu) h
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu r) (norm_nonneg _)

theorem conv_mono {P : PowerSeries ℂ} {ρ ρ' : ℝ} (h : PSConv P ρ) (h0 : 0 ≤ ρ') (hle : ρ' ≤ ρ) :
    PSConv P ρ' :=
  h.of_nonneg_of_le (fun r => mul_nonneg (norm_nonneg _) (pow_nonneg h0 r))
    (fun r => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle r) (norm_nonneg _))

/-! ## §2 Cauchy products -/

theorem coeff_mul_norm_le (P Q : PowerSeries ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ‖PowerSeries.coeff n (P * Q)‖ * ρ ^ n ≤
      ∑ kl ∈ Finset.antidiagonal n, (‖PowerSeries.coeff kl.1 P‖ * ρ ^ kl.1) *
        (‖PowerSeries.coeff kl.2 Q‖ * ρ ^ kl.2) := by
  rw [PowerSeries.coeff_mul]
  calc ‖∑ kl ∈ Finset.antidiagonal n, PowerSeries.coeff kl.1 P * PowerSeries.coeff kl.2 Q‖ *
        ρ ^ n ≤ (∑ kl ∈ Finset.antidiagonal n,
          ‖PowerSeries.coeff kl.1 P‖ * ‖PowerSeries.coeff kl.2 Q‖) * ρ ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hρ n)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun kl _ => ?_)
        rw [norm_mul]
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        rw [Finset.mem_antidiagonal] at hkl
        rw [← hkl, pow_add]; ring

theorem conv_mul {P Q : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hP : PSConv P ρ)
    (hQ : PSConv Q ρ) : PSConv (P * Q) ρ ∧ psMass (P * Q) ρ ≤ psMass P ρ * psMass Q ρ := by
  have hf : Summable fun r => ‖‖PowerSeries.coeff r P‖ * ρ ^ r‖ :=
    hP.congr fun r => (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hρ r))).symm
  have hg : Summable fun r => ‖‖PowerSeries.coeff r Q‖ * ρ ^ r‖ :=
    hQ.congr fun r => (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hρ r))).symm
  have hfg := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  have hfg' : Summable fun n => ∑ kl ∈ Finset.antidiagonal n,
      (‖PowerSeries.coeff kl.1 P‖ * ρ ^ kl.1) * (‖PowerSeries.coeff kl.2 Q‖ * ρ ^ kl.2) :=
    hfg.of_norm
  have hc : PSConv (P * Q) ρ :=
    hfg'.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ n))
      (coeff_mul_norm_le P Q hρ)
  refine ⟨hc, ?_⟩
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  unfold psMass
  rw [heq]
  exact Summable.tsum_le_tsum (coeff_mul_norm_le P Q hρ) hc hfg'

theorem psEval_mul {P Q : PowerSeries ℂ} {ρ : ℝ} (hP : PSConv P ρ) (hQ : PSConv Q ρ)
    {u : ℂ} (hu : ‖u‖ ≤ ρ) : psEval (P * Q) u = psEval P u * psEval Q u := by
  have hf := summable_norm_of_conv hP hu
  have hg := summable_norm_of_conv hQ hu
  unfold psEval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

theorem conv_one (ρ : ℝ) : PSConv 1 ρ := by
  refine summable_of_ne_finset_zero (s := {0}) fun r hr => ?_
  rw [Finset.mem_singleton] at hr
  simp [PowerSeries.coeff_one, hr]

theorem psMass_one {ρ : ℝ} : psMass 1 ρ = 1 := by
  unfold psMass
  rw [tsum_eq_single 0 (fun r hr => by simp [PowerSeries.coeff_one, hr])]
  simp

theorem psEval_one (u : ℂ) : psEval 1 u = 1 := by
  unfold psEval
  rw [tsum_eq_single 0 (fun r hr => by simp [PowerSeries.coeff_one, hr])]
  simp

theorem conv_pow {P : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hP : PSConv P ρ) (m : ℕ) :
    PSConv (P ^ m) ρ ∧ psMass (P ^ m) ρ ≤ psMass P ρ ^ m := by
  induction m with
  | zero => simp only [pow_zero]; exact ⟨conv_one ρ, psMass_one.le⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := conv_mul hρ ih.1 hP
    refine ⟨by rw [pow_succ]; exact h1, ?_⟩
    rw [pow_succ, pow_succ]
    exact h2.trans (mul_le_mul_of_nonneg_right ih.2 (psMass_nonneg P hρ))

theorem psEval_pow {P : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hP : PSConv P ρ) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) (m : ℕ) : psEval (P ^ m) u = psEval P u ^ m := by
  induction m with
  | zero => simp only [pow_zero]; exact psEval_one u
  | succ m ih =>
    rw [pow_succ, psEval_mul (conv_pow hρ hP m).1 hP hu, ih, pow_succ]

/-! ## §3 The exponential and the unit `E(z) = (e^z − 1)/z` -/

/-- The series of `e^{αz}`. -/
def expA (α : ℂ) : PowerSeries ℂ := PowerSeries.rescale α (PowerSeries.exp ℂ)

theorem coeff_expA (α : ℂ) (r : ℕ) :
    PowerSeries.coeff r (expA α) = α ^ r / (r.factorial : ℂ) := by
  rw [expA, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

theorem hasSum_expA (α u : ℂ) :
    HasSum (fun r => PowerSeries.coeff r (expA α) * u ^ r) (exp (α * u)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (α * u)
  rw [← Complex.exp_eq_exp_ℂ] at h
  refine h.congr_fun fun r => ?_
  rw [coeff_expA, mul_pow]; ring

theorem conv_expA (α : ℂ) {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    PSConv (expA α) ρ ∧ psMass (expA α) ρ = Real.exp (‖α‖ * ρ) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (‖α‖ * ρ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have he : ∀ r : ℕ, ‖PowerSeries.coeff r (expA α)‖ * ρ ^ r = (‖α‖ * ρ) ^ r / r.factorial := by
    intro r
    rw [coeff_expA, norm_div, norm_pow, Complex.norm_natCast, mul_pow]; ring
  have h' : HasSum (fun r => ‖PowerSeries.coeff r (expA α)‖ * ρ ^ r) (Real.exp (‖α‖ * ρ)) :=
    h.congr_fun he
  exact ⟨h'.summable, h'.tsum_eq⟩

theorem psEval_expA (α : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    psEval (expA α) u = exp (α * u) :=
  (hasSum_psEval (conv_expA α hρ).1 hu).unique (hasSum_expA α u)

theorem coeff_unit (r : ℕ) :
    PowerSeries.coeff r exponentialUnit = ((r + 1).factorial : ℂ)⁻¹ := by
  simp [exponentialUnit]

theorem norm_coeff_unit_sub_one_le (r : ℕ) :
    ‖PowerSeries.coeff r (exponentialUnit - 1)‖ ≤ if r = 0 then 0 else 1 := by
  rcases r with _ | r
  · simp
  · simp only [map_sub, coeff_unit, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, sub_zero,
      norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _))

/-- The unit minus one converges at every `ρ < 1`, with mass at most `ρ/(1−ρ)`. -/
theorem conv_unit_sub_one {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    PSConv (exponentialUnit - 1) ρ ∧ psMass (exponentialUnit - 1) ρ ≤ ρ / (1 - ρ) := by
  have hg : HasSum (fun r : ℕ => (if r = 0 then (0 : ℝ) else 1) * ρ ^ r) (ρ / (1 - ρ)) := by
    have h := (hasSum_geometric_of_lt_one hρ hρ1)
    have h2 : HasSum (fun r : ℕ => ρ ^ r - (if r = 0 then (1 : ℝ) else 0)) ((1 - ρ)⁻¹ - 1) :=
      h.sub (hasSum_ite_eq 0 1)
    convert h2 using 1
    · funext r; split_ifs with hr <;> simp [hr]
    · field_simp [show (1 - ρ) ≠ 0 by linarith]; ring
  have hle : ∀ r : ℕ, ‖PowerSeries.coeff r (exponentialUnit - 1)‖ * ρ ^ r ≤
      (if r = 0 then (0 : ℝ) else 1) * ρ ^ r := fun r =>
    mul_le_mul_of_nonneg_right (norm_coeff_unit_sub_one_le r) (pow_nonneg hρ r)
  have hc : PSConv (exponentialUnit - 1) ρ :=
    hg.summable.of_nonneg_of_le (fun r => mul_nonneg (norm_nonneg _) (pow_nonneg hρ r)) hle
  exact ⟨hc, (Summable.tsum_le_tsum hle hc hg.summable).trans hg.tsum_eq.le⟩

theorem conv_unit {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    PSConv exponentialUnit ρ ∧ psMass exponentialUnit ρ ≤ 1 + ρ / (1 - ρ) := by
  have h := conv_unit_sub_one hρ hρ1
  have hsum : exponentialUnit = (exponentialUnit - 1) + 1 := by ring
  have hc1 := conv_one ρ
  have hc : PSConv exponentialUnit ρ := by
    rw [hsum]
    refine (h.1.add hc1).of_nonneg_of_le (fun r => mul_nonneg (norm_nonneg _) (pow_nonneg hρ r))
      fun r => ?_
    rw [map_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hρ r)
  refine ⟨hc, ?_⟩
  have hle : ∀ r : ℕ, ‖PowerSeries.coeff r exponentialUnit‖ * ρ ^ r ≤
      ‖PowerSeries.coeff r (exponentialUnit - 1)‖ * ρ ^ r +
        ‖PowerSeries.coeff r (1 : PowerSeries ℂ)‖ * ρ ^ r := by
    intro r
    conv_lhs => rw [hsum]
    rw [map_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hρ r)
  calc psMass exponentialUnit ρ ≤ ∑' r, (‖PowerSeries.coeff r (exponentialUnit - 1)‖ * ρ ^ r +
        ‖PowerSeries.coeff r (1 : PowerSeries ℂ)‖ * ρ ^ r) :=
          Summable.tsum_le_tsum hle hc (h.1.add hc1)
    _ = psMass (exponentialUnit - 1) ρ + psMass 1 ρ := Summable.tsum_add h.1 hc1
    _ ≤ ρ / (1 - ρ) + 1 := by rw [psMass_one]; linarith [h.2]
    _ = 1 + ρ / (1 - ρ) := by ring

/-- `u · E(u) = e^u − 1`. -/
theorem psEval_unit_mul {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    u * psEval exponentialUnit u = exp u - 1 := by
  have h := hasSum_psEval (conv_unit hρ hρ1).1 hu
  have h2 : HasSum (fun r : ℕ => u ^ (r + 1) / ((r + 1).factorial : ℂ)) (exp u - 1) := by
    have he := NormedSpace.expSeries_div_hasSum_exp u
    rw [← Complex.exp_eq_exp_ℂ] at he
    have := (hasSum_nat_add_iff' 1).mpr he
    simpa using this
  have h3 := h.mul_left u
  refine h3.unique (h2.congr_fun fun r => ?_)
  rw [coeff_unit, pow_succ]; field_simp

theorem psEval_unit_sub_one {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    psEval (exponentialUnit - 1) u = psEval exponentialUnit u - 1 := by
  have h1 := hasSum_psEval (conv_unit hρ hρ1).1 hu
  have h2 := hasSum_psEval (conv_one ρ) hu
  rw [psEval_one] at h2
  have h3 := hasSum_psEval (conv_unit_sub_one hρ hρ1).1 hu
  refine h3.unique ((h1.sub h2).congr_fun fun r => ?_)
  rw [map_sub, sub_mul]

theorem norm_psEval_unit_sub_one_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) : ‖psEval exponentialUnit u - 1‖ ≤ ρ / (1 - ρ) := by
  rw [← psEval_unit_sub_one hρ hρ1 hu]
  have h := conv_unit_sub_one hρ hρ1
  exact (norm_tsum_le_tsum_norm (summable_norm_of_conv h.1 hu)).trans
    ((tsum_norm_le_psMass h.1 hu).trans h.2)

/-! ## §4 The complex power `E^b` -/

theorem coeff_unit_sub_one_pow_eq_zero {d r : ℕ} (h : r < d) :
    PowerSeries.coeff r ((exponentialUnit - 1) ^ d) = 0 := by
  have hX : exponentialUnit - 1 = PowerSeries.X * PowerSeries.mk (fun r =>
      PowerSeries.coeff (r + 1) (exponentialUnit - 1)) := by
    ext n
    rcases n with _ | n
    · simp [coeff_unit]
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
  rw [hX, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [not_le.mpr h]

/-- `x := ρ/(1−ρ) ≤ 1/2` for `ρ ≤ 1/3`. -/
theorem ratio_le_half {ρ : ℝ} (_hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) : ρ / (1 - ρ) ≤ 1 / 2 := by
  rw [div_le_iff₀ (by linarith)]; linarith

theorem summable_binomial (b : ℂ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun d : ℕ => ‖Ring.choose b d‖ * x ^ d) := by
  have hr : ((Real.toNNReal x : NNReal) : ENNReal) < (binomialSeries ℂ b).radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr (Real.toNNReal_lt_one.mpr hx1))
      binomialSeries_radius_ge_one
  have h := (binomialSeries ℂ b).summable_norm_mul_pow hr
  refine h.congr fun d => ?_
  rw [Real.coe_toNNReal _ hx]
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_norm]

theorem hasSum_binomial (b : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun d : ℕ => Ring.choose b d * w ^ d) ((1 + w) ^ b) := by
  have hy : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    exact ENNReal.coe_lt_one_iff.mpr (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hw)
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := b)).hasSum hy
  simp only [zero_add] at h
  refine h.congr_fun fun d => ?_
  rw [binomialSeries_apply]
  simp [List.ofFn_const, List.prod_replicate, smul_eq_mul]

/-- The double majorant of the binomial substitution. -/
def binTerm (b : ℂ) (ρ : ℝ) (p : ℕ × ℕ) : ℝ :=
  ‖Ring.choose b p.1‖ * (‖PowerSeries.coeff p.2 ((exponentialUnit - 1) ^ p.1)‖ * ρ ^ p.2)

/-- **The formal complex power of the unit converges, with a binomial majorant.** -/
theorem conv_unitPower (b : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) :
    PSConv (exponentialUnitPower b) ρ ∧
      psMass (exponentialUnitPower b) ρ ≤ ∑' d : ℕ, ‖Ring.choose b d‖ * (ρ / (1 - ρ)) ^ d := by
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = ρ / (1 - ρ) := ⟨_, rfl⟩
  rw [← hx]
  have hx0 : 0 ≤ x := hx ▸ div_nonneg hρ (by linarith)
  have hx1 : x < 1 := hx ▸ lt_of_le_of_lt (ratio_le_half hρ hρ3) (by norm_num)
  have hE := conv_unit_sub_one hρ hρ1
  rw [← hx] at hE
  have hpow : ∀ d, PSConv ((exponentialUnit - 1) ^ d) ρ ∧
      psMass ((exponentialUnit - 1) ^ d) ρ ≤ x ^ d := fun d => by
    obtain ⟨h1, h2⟩ := conv_pow hρ hE.1 d
    exact ⟨h1, h2.trans (pow_le_pow_left₀ (psMass_nonneg _ hρ) hE.2 d)⟩
  -- the double majorant
  let g : ℕ × ℕ → ℝ := binTerm b ρ
  have hg : ∀ p, g p = ‖Ring.choose b p.1‖ *
      (‖PowerSeries.coeff p.2 ((exponentialUnit - 1) ^ p.1)‖ * ρ ^ p.2) := fun p => rfl
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (pow_nonneg hρ _))
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun d => ((hpow d).1.mul_left
      ‖Ring.choose b d‖).congr fun r => (hg (d, r)).symm, ?_⟩
    refine (summable_binomial b hx0 hx1).of_nonneg_of_le
      (fun d => tsum_nonneg fun r => hg0 _) fun d => ?_
    simp only [hg]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)
  -- coefficient bound
  have hcol : ∀ r, Summable fun d => g (d, r) := fun r => hgs.prod_symm.prod_factor r
  have hcoef : ∀ r, ‖PowerSeries.coeff r (exponentialUnitPower b)‖ * ρ ^ r ≤
      ∑' d, g (d, r) := by
    intro r
    have hfin : (∑ᶠ d : ℕ, Ring.choose b d * PowerSeries.coeff r ((exponentialUnit - 1) ^ d)) =
        ∑ d ∈ Finset.range (r + 1),
          Ring.choose b d * PowerSeries.coeff r ((exponentialUnit - 1) ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdr
      exact hd (by rw [coeff_unit_sub_one_pow_eq_zero (by omega), mul_zero])
    rw [exponentialUnitPower_coeff, hfin]
    calc ‖∑ d ∈ Finset.range (r + 1),
          Ring.choose b d * PowerSeries.coeff r ((exponentialUnit - 1) ^ d)‖ * ρ ^ r
        ≤ (∑ d ∈ Finset.range (r + 1), ‖Ring.choose b d‖ *
            ‖PowerSeries.coeff r ((exponentialUnit - 1) ^ d)‖) * ρ ^ r := by
          refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun d _ => (norm_mul _ _).le)) (pow_nonneg hρ r)
      _ = ∑ d ∈ Finset.range (r + 1), g (d, r) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => by rw [hg]; ring
      _ ≤ ∑' d, g (d, r) := Summable.sum_le_tsum _ (fun d _ => hg0 _) (hcol r)
  have hrows : Summable fun r => ∑' d, g (d, r) := hgs.prod_symm.prod
  have hc : PSConv (exponentialUnitPower b) ρ :=
    hrows.of_nonneg_of_le (fun r => mul_nonneg (norm_nonneg _) (pow_nonneg hρ r)) hcoef
  refine ⟨hc, ?_⟩
  have e1 : ∑' r, ∑' d, g (d, r) = ∑' p : ℕ × ℕ, g p.swap := hgs.prod_symm.tsum_prod.symm
  have e2 : ∑' p : ℕ × ℕ, g p.swap = ∑' p, g p := (Equiv.prodComm ℕ ℕ).tsum_eq g
  have e3 : ∑' p, g p = ∑' d, ∑' r, g (d, r) := hgs.tsum_prod
  have hrow : ∀ d, ∑' r, g (d, r) ≤ ‖Ring.choose b d‖ * x ^ d := by
    intro d
    simp only [hg]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)
  calc psMass (exponentialUnitPower b) ρ ≤ ∑' r, ∑' d, g (d, r) :=
        Summable.tsum_le_tsum hcoef hc hrows
    _ = ∑' d, ∑' r, g (d, r) := by rw [e1, e2, e3]
    _ ≤ _ := Summable.tsum_le_tsum hrow hgs.prod (summable_binomial b hx0 hx1)

theorem summable_binTerm (b : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) :
    Summable (binTerm b ρ) := by
  have hρ1 : ρ < 1 := by linarith
  have hx0 : 0 ≤ ρ / (1 - ρ) := div_nonneg hρ (by linarith)
  have hx1 : ρ / (1 - ρ) < 1 := lt_of_le_of_lt (ratio_le_half hρ hρ3) (by norm_num)
  have hE := conv_unit_sub_one hρ hρ1
  have hpow : ∀ d, PSConv ((exponentialUnit - 1) ^ d) ρ ∧
      psMass ((exponentialUnit - 1) ^ d) ρ ≤ (ρ / (1 - ρ)) ^ d := fun d => by
    obtain ⟨h1, h2⟩ := conv_pow hρ hE.1 d
    exact ⟨h1, h2.trans (pow_le_pow_left₀ (psMass_nonneg _ hρ) hE.2 d)⟩
  have hg0 : ∀ p, 0 ≤ binTerm b ρ p := fun p => mul_nonneg (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (pow_nonneg hρ _))
  refine (summable_prod_of_nonneg hg0).mpr ⟨fun d => ((hpow d).1.mul_left
    ‖Ring.choose b d‖).congr fun r => rfl, ?_⟩
  refine (summable_binomial b hx0 hx1).of_nonneg_of_le
    (fun d => tsum_nonneg fun r => hg0 _) fun d => ?_
  change ∑' r, ‖Ring.choose b d‖ * (‖PowerSeries.coeff r ((exponentialUnit - 1) ^ d)‖ * ρ ^ r)
    ≤ _
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)

/-- **The formal complex power of the unit evaluates to the principal power**
`E(u)^b = exp(b log E(u))`, for `‖u‖ ≤ ρ ≤ 1/3`. -/
theorem psEval_unitPower (b : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) {u : ℂ}
    (hu : ‖u‖ ≤ ρ) :
    psEval (exponentialUnitPower b) u = psEval exponentialUnit u ^ b := by
  have hρ1 : ρ < 1 := by linarith
  have hw : ‖psEval exponentialUnit u - 1‖ < 1 :=
    (norm_psEval_unit_sub_one_le hρ hρ1 hu).trans_lt
      (lt_of_le_of_lt (ratio_le_half hρ hρ3) (by norm_num))
  have hbin := hasSum_binomial b hw
  rw [add_sub_cancel] at hbin
  have hE := conv_unit_sub_one hρ hρ1
  let f : ℕ × ℕ → ℂ := fun p => Ring.choose b p.1 *
    (PowerSeries.coeff p.2 ((exponentialUnit - 1) ^ p.1) * u ^ p.2)
  have hfb : ∀ p, ‖f p‖ ≤ binTerm b ρ p := by
    intro p
    change ‖Ring.choose b p.1 * (PowerSeries.coeff p.2 ((exponentialUnit - 1) ^ p.1) *
      u ^ p.2)‖ ≤ _
    rw [norm_mul, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg u) hu _) (norm_nonneg _)) (norm_nonneg _)
  have hf : Summable f := Summable.of_norm_bounded (summable_binTerm b hρ hρ3) hfb
  -- rows
  have hrow : ∀ d, ∑' r, f (d, r) = Ring.choose b d * (psEval exponentialUnit u - 1) ^ d := by
    intro d
    change ∑' r, Ring.choose b d * (PowerSeries.coeff r ((exponentialUnit - 1) ^ d) * u ^ r) = _
    rw [tsum_mul_left]
    congr 1
    change psEval ((exponentialUnit - 1) ^ d) u = _
    rw [psEval_pow hρ hE.1 hu, psEval_unit_sub_one hρ hρ1 hu]
  -- columns
  have hcolv : ∀ r, ∑' d, f (d, r) =
      PowerSeries.coeff r (exponentialUnitPower b) * u ^ r := by
    intro r
    have hz : ∀ d ∉ Finset.range (r + 1), f (d, r) = 0 := by
      intro d hd
      rw [Finset.mem_range, not_lt] at hd
      change Ring.choose b d * (PowerSeries.coeff r ((exponentialUnit - 1) ^ d) * u ^ r) = 0
      rw [coeff_unit_sub_one_pow_eq_zero (by omega), zero_mul, mul_zero]
    rw [tsum_eq_sum hz, exponentialUnitPower_coeff,
      finsum_eq_sum_of_support_subset (s := Finset.range (r + 1)), Finset.sum_mul]
    · exact Finset.sum_congr rfl fun d _ => by
        change Ring.choose b d * (PowerSeries.coeff r ((exponentialUnit - 1) ^ d) * u ^ r) = _
        ring
    · intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdr
      exact hd (by rw [coeff_unit_sub_one_pow_eq_zero (by omega), mul_zero])
  have e1 : psEval (exponentialUnitPower b) u = ∑' r, ∑' d, f (d, r) := by
    unfold psEval
    exact tsum_congr fun r => (hcolv r).symm
  have e2 : ∑' r, ∑' d, f (d, r) = ∑' p : ℕ × ℕ, f p.swap := hf.prod_symm.tsum_prod.symm
  have e3 : ∑' p : ℕ × ℕ, f p.swap = ∑' p, f p := (Equiv.prodComm ℕ ℕ).tsum_eq f
  rw [e1, e2, e3, hf.tsum_prod, tsum_congr hrow]
  exact hbin.tsum_eq

/-- `E^{b+m} = E^b · E^m` formally. -/
theorem unitPower_add_nat (b : ℂ) (m : ℕ) :
    exponentialUnitPower (b + m) = exponentialUnitPower b * exponentialUnit ^ m := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero' exponentialUnit_sub_one_constant
  rw [exponentialUnitPower, exponentialUnitPower, PowerSeries.binomialSeries_add,
    PowerSeries.subst_mul ha, PowerSeries.binomialSeries_nat, PowerSeries.subst_pow ha,
    PowerSeries.subst_add ha, PowerSeries.subst_X ha]
  congr 2
  have h1 : PowerSeries.subst (exponentialUnit - 1) (1 : PowerSeries ℂ) = 1 := by
    rw [← map_one (PowerSeries.C (R := ℂ)), PowerSeries.subst_C]
    rfl
  rw [h1]
  ring

/-! ## §5 The bracket factor -/

/-- The series `e^{αz} E^{c'} E^m`. -/
def bracketFactor (α c' : ℂ) (m : ℕ) : PowerSeries ℂ :=
  expA α * exponentialUnitPower c' * exponentialUnit ^ m

/-- The explicit bracket coefficients are those of `bracketFactor`. -/
theorem bracketCoeff_eq (α n c' : ℂ) (m r : ℕ) (h : -n - r - 1 = c' + m) :
    bracketCoeff α n r = PowerSeries.coeff r (bracketFactor α c' m) := by
  rw [bracketCoeff, h, unitPower_add_nat, bracketFactor, expA, mul_assoc]

theorem conv_bracketFactor (α c' : ℂ) (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) :
    PSConv (bracketFactor α c' m) ρ ∧ psMass (bracketFactor α c' m) ρ ≤
      Real.exp (‖α‖ * ρ) * psMass (exponentialUnitPower c') ρ *
        psMass exponentialUnit ρ ^ m := by
  have hρ1 : ρ < 1 := by linarith
  have h1 := conv_expA α hρ
  have h2 := conv_unitPower c' hρ hρ3
  have h3 := conv_pow hρ (conv_unit hρ hρ1).1 m
  have h12 := conv_mul hρ h1.1 h2.1
  have h123 := conv_mul hρ h12.1 h3.1
  refine ⟨h123.1, h123.2.trans ?_⟩
  rw [← h1.2]
  exact mul_le_mul h12.2 h3.2 (psMass_nonneg _ hρ)
    (mul_nonneg (psMass_nonneg _ hρ) (psMass_nonneg _ hρ))

theorem psEval_bracketFactor (α c' : ℂ) (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3)
    {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    psEval (bracketFactor α c' m) u =
      exp (α * u) * psEval exponentialUnit u ^ c' * psEval exponentialUnit u ^ m := by
  have hρ1 : ρ < 1 := by linarith
  have h1 := conv_expA α hρ
  have h2 := conv_unitPower c' hρ hρ3
  have h3 := (conv_unit hρ hρ1).1
  rw [bracketFactor, psEval_mul (conv_mul hρ h1.1 h2.1).1 (conv_pow hρ h3 m).1 hu,
    psEval_mul h1.1 h2.1 hu, psEval_expA α hρ hu, psEval_unitPower c' hρ hρ3 hu,
    psEval_pow hρ h3 hu]

end VOA.Huang.GenusOneG1e
