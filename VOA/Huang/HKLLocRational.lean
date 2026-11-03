/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# HKL locality, the analytic-to-formal step: a gluing criterion for Laurent coefficients

Let `s, t : ℤ → ℂ` with `s n = 0` for `n ≫ 0` and `t n = 0` for `n ≪ 0`.  Suppose there is one
function `Ψ`, holomorphic on `ℂ ∖ {0, 1}`, with

* `Ψ ζ = Σₙ s n ζⁿ` on `‖ζ‖ > 1` (the expansion at `∞`),
* `Ψ ζ = Σₙ t n ζⁿ` on `0 < ‖ζ‖ < 1` (the expansion at `0`),
* `(ζ - 1)ᴺ Ψ ζ` bounded near `ζ = 1` (a pole of order `≤ N`).

Then the two formal series agree after multiplication by `(ζ - 1)ᴺ`:

  `Σ_{i ≤ N} (-1)^{N-i} C(N,i) (s (k - i) - t (k - i)) = 0`  for every `k`

(`conv_eq_of_glue`).  This is the formal shadow of "the four-point function is a rational
function with poles only at `0, 1, ∞`": for a vertex operator algebra extension it turns the
analytic commutativity of `Y_W(a, z₁) Y_W(b, z₂)` into the formal locality
`(z₁ - z₂)ᴺ [Y_W(a, z₁), Y_W(b, z₂)] = 0`.

Proof: with `α = conv t`, `β = conv s` (the coefficients of `(ζ-1)ᴺ Ψ` at `0` and at `∞`), the
function `H = (ζ-1)ᴺ Ψ - (principal part of α at 0) - (polynomial part of β)` is entire after
removing the bounded singularity at `1`, and tends to `0` at infinity; Liouville gives `H = 0`,
and uniqueness of power-series coefficients (at `0`, and at `∞` in `w = 1/ζ`) gives `α = β`.

Mathlib only.  No `sorry`, no axioms.
-/

noncomputable section

namespace VOA.Huang.HKLLoc

open Complex Filter Topology Set
open scoped BigOperators

/-! ## Coefficients of `(ζ - 1)ᴺ · Σ u n ζⁿ` -/

/-- The coefficients of `(ζ - 1)ᴺ · Σₙ u n ζⁿ`. -/
def conv (N : ℕ) (u : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (N + 1), ((-1 : ℂ) ^ (N - i) * (N.choose i : ℂ)) * u (k - i)

theorem hasSum_shift {u : ℤ → ℂ} {ζ X : ℂ} (hζ : ζ ≠ 0)
    (h : HasSum (fun n : ℤ => u n * ζ ^ n) X) (i : ℕ) :
    HasSum (fun k : ℤ => u (k - i) * ζ ^ k) (ζ ^ i * X) := by
  have h1 := h.mul_left (ζ ^ i)
  rw [← (Equiv.subRight (i : ℤ)).hasSum_iff] at h1
  convert h1 using 1
  funext k
  simp only [Function.comp_apply, Equiv.subRight_apply]
  rw [← zpow_natCast, mul_left_comm, ← zpow_add₀ hζ, add_sub_cancel]

theorem hasSum_conv (N : ℕ) {u : ℤ → ℂ} {ζ X : ℂ} (hζ : ζ ≠ 0)
    (h : HasSum (fun n : ℤ => u n * ζ ^ n) X) :
    HasSum (fun k : ℤ => conv N u k * ζ ^ k) ((ζ - 1) ^ N * X) := by
  have hs := hasSum_sum (s := Finset.range (N + 1)) fun i _ =>
    (hasSum_shift hζ h i).mul_left ((-1 : ℂ) ^ (N - i) * (N.choose i : ℂ))
  have e : (ζ - 1) ^ N * X = ∑ i ∈ Finset.range (N + 1),
      ((-1 : ℂ) ^ (N - i) * (N.choose i : ℂ)) * (ζ ^ i * X) := by
    rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  convert hs using 1
  funext k
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem conv_eq_zero_of_lt {N : ℕ} {u : ℤ → ℂ} {n₁ : ℤ} (hu : ∀ n, n < n₁ → u n = 0) {k : ℤ}
    (hk : k < n₁) : conv N u k = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [hu (k - i) (by omega), mul_zero]

theorem conv_eq_zero_of_gt {N : ℕ} {u : ℤ → ℂ} {n₀ : ℤ} (hu : ∀ n, n₀ < n → u n = 0) {k : ℤ}
    (hk : n₀ + N < k) : conv N u k = 0 :=
  Finset.sum_eq_zero fun i hi => by
    rw [Finset.mem_range] at hi
    rw [hu (k - i) (by omega), mul_zero]

theorem conv_sub (N : ℕ) (u v : ℤ → ℂ) (k : ℤ) :
    conv N u k - conv N v k = conv N (u - v) k := by
  simp only [conv, ← Finset.sum_sub_distrib, Pi.sub_apply, mul_sub]

/-! ## Uniqueness of power-series coefficients -/

/-- A power series whose sum vanishes on the punctured unit disc is zero. -/
theorem coeffs_eq_zero_of_hasSum_zero' (d : ℕ → ℂ)
    (h : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → HasSum (fun n => d n * q ^ n) 0) : d = 0 := by
  set p := FormalMultilinearSeries.ofScalars ℂ d with hp
  have hrad : (((1 / 2 : NNReal)) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_tendsto (l := 0) ?_
    have := (h (1 / 2 : ℂ) (by norm_num) (by norm_num)).summable.tendsto_atTop_zero.norm
    simp only [norm_zero] at this
    refine this.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
    norm_num
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hF := p.hasFPowerSeriesOnBall hpos
  have hzero : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q hq0 hq1
    rw [FormalMultilinearSeries.sum]
    simp_rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    exact (h q hq0 hq1).tsum_eq
  have h0 : p.sum 0 = 0 := by
    have hc := hF.hasFPowerSeriesAt.continuousAt
    have h1 : Tendsto p.sum (𝓝[≠] 0) (𝓝 (p.sum 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto p.sum (𝓝[≠] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with q hq hq'
      rw [hzero q hq (by simpa using hq')]
    exact tendsto_nhds_unique h1 h2
  have hev : p.sum =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · rw [hq0, h0]; rfl
    · exact hzero q hq0 (by simpa using hq)
  have := (hF.hasFPowerSeriesAt.congr hev).eq_zero
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ)).1 this

/-- A power series summable on the open unit disc is holomorphic there. -/
theorem differentiableAt_powerSeries (a : ℕ → ℂ)
    (ha : ∀ q : ℂ, ‖q‖ < 1 → Summable fun n => a n * q ^ n) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q => ∑' n, a n * q ^ n) z := by
  set p := FormalMultilinearSeries.ofScalars ℂ a with hp
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hr1' : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hrad : ((r.toNNReal : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_tendsto (l := 0) ?_
    have := (ha (r : ℂ) hr1').tendsto_atTop_zero.norm
    simp only [norm_zero] at this
    refine this.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0, Real.coe_toNNReal r hr0]
  have hrpos : (0 : ENNReal) < ((r.toNNReal : NNReal) : ENNReal) := by
    rw [ENNReal.coe_pos, Real.toNNReal_pos]
    exact lt_of_le_of_lt (norm_nonneg z) hzr
  have hF := (p.hasFPowerSeriesOnBall (lt_of_lt_of_le hrpos hrad)).mono hrpos hrad
  have hzmem : z ∈ Metric.eball (0 : ℂ) ((r.toNNReal : NNReal) : ENNReal) := by
    change edist z 0 < _
    rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _)
      ENNReal.coe_ne_top, ENNReal.coe_toReal, Real.coe_toNNReal r hr0]
    exact hzr
  have hfeq : p.sum = fun q => ∑' n, a n * q ^ n := by
    funext q
    rw [FormalMultilinearSeries.sum]
    simp_rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← hfeq]
  exact (hF.analyticAt_of_mem hzmem).differentiableAt

/-! ## The gluing criterion -/

/-- Splitting a `ℤ`-indexed sum at `0`, with finitely many negative terms. -/
theorem hasSum_nat_of_int {α : ℤ → ℂ} {ζ X : ℂ} (L : ℕ)
    (hαneg : ∀ k : ℕ, L ≤ k → α (-((k : ℤ) + 1)) = 0)
    (h : HasSum (fun k : ℤ => α k * ζ ^ k) X) :
    HasSum (fun k : ℕ => α k * ζ ^ k)
      (X - ∑ k ∈ Finset.range L, α (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))) := by
  have hneg : HasSum (fun k : ℕ => α (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1)))
      (∑ k ∈ Finset.range L, α (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      rw [hαneg k hk, zero_mul]
  have hpos : Summable fun k : ℕ => α k * ζ ^ (k : ℤ) :=
    h.summable.comp_injective Nat.cast_injective
  have e := h.unique (hpos.hasSum.of_nat_of_neg_add_one hneg)
  rw [e, add_sub_cancel_right]
  simpa only [zpow_natCast] using hpos.hasSum

/-- Splitting a `ℤ`-indexed sum at `∞`, with finitely many positive terms. -/
theorem hasSum_split_inf {β : ℤ → ℂ} {ζ X : ℂ} (M : ℕ)
    (hβpos : ∀ k : ℕ, M + 1 ≤ k → β k = 0)
    (h : HasSum (fun k : ℤ => β k * ζ ^ k) X) :
    HasSum (fun k : ℕ => β (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1)))
      (X - ∑ k ∈ Finset.range (M + 1), β k * ζ ^ k) := by
  have hpos : HasSum (fun k : ℕ => β k * ζ ^ (k : ℤ))
      (∑ k ∈ Finset.range (M + 1), β k * ζ ^ k) := by
    refine (hasSum_sum_of_ne_finset_zero (s := Finset.range (M + 1))
      (f := fun k : ℕ => β k * ζ ^ k) fun k hk => ?_).congr_fun fun k => ?_
    · rw [Finset.mem_range, not_lt] at hk
      change β k * ζ ^ k = 0
      rw [hβpos k hk, zero_mul]
    · simp only [zpow_natCast]
  have hnegS : Summable fun k : ℕ => β (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1)) :=
    h.summable.comp_injective (fun a b h => by simpa using h)
  have e := h.unique (hpos.of_nat_of_neg_add_one hnegS.hasSum)
  rw [e, add_sub_cancel_left]
  exact hnegS.hasSum

theorem neg_succ_zpow (ζ : ℂ) (k : ℕ) : ζ ^ (-((k : ℤ) + 1)) = (ζ⁻¹) ^ (k + 1) := by
  rw [show (-((k : ℤ) + 1)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    inv_pow]

/-- The `‖ζ‖ ≥ 2` bound for the tail at infinity. -/
theorem norm_tail_le {β : ℤ → ℂ} {ζ : ℂ} (hζ : 2 ≤ ‖ζ‖)
    (hβ2 : Summable fun k : ℕ => ‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1))
    {V : ℂ} (hV : HasSum (fun k : ℕ => β (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))) V) :
    ‖V‖ ≤ (2 * ∑' k : ℕ, ‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1)) / ‖ζ‖ := by
  have hn0 : 0 < ‖ζ‖ := by linarith
  have hterm : ∀ k : ℕ, ‖β (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))‖ ≤
      (2 * (‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1))) / ‖ζ‖ := by
    intro k
    rw [norm_mul, neg_succ_zpow, norm_pow, norm_inv, inv_pow]
    have hp : 2 ^ k * ‖ζ‖ ≤ ‖ζ‖ ^ (k + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hζ k) hn0.le
    have hpos : 0 < ‖ζ‖ ^ (k + 1) := pow_pos hn0 _
    have e2 : (2 : ℝ) * (1 / 2) ^ (k + 1) = (2 ^ k)⁻¹ := by
      rw [pow_succ, one_div, inv_pow]; field_simp
    rw [le_div_iff₀ hn0, show 2 * (‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1)) =
      ‖β (-((k : ℤ) + 1))‖ * (2 * (1 / 2) ^ (k + 1)) by ring, e2]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_mul_eq_div, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hmaj : Summable fun k : ℕ =>
      (2 * (‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1))) / ‖ζ‖ :=
    (hβ2.mul_left 2).div_const _
  rw [← hV.tsum_eq]
  have hns := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hmaj
  refine (norm_tsum_le_tsum_norm hns).trans ?_
  refine (Summable.tsum_le_tsum hterm hns hmaj).trans ?_
  rw [tsum_div_const, tsum_mul_left]

/-- The `‖ζ‖ ≥ 1` bound for a finite principal part at `0`. -/
theorem norm_principal_le {α : ℤ → ℂ} {ζ : ℂ} (L : ℕ) (hζ : 1 ≤ ‖ζ‖) :
    ‖∑ k ∈ Finset.range L, α (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))‖ ≤
      (∑ k ∈ Finset.range L, ‖α (-((k : ℤ) + 1))‖) / ‖ζ‖ := by
  have hn0 : 0 < ‖ζ‖ := by linarith
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, neg_succ_zpow, norm_pow, norm_inv, inv_pow, le_div_iff₀ hn0, mul_assoc]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hn0.ne', mul_one]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hζ)

/-- **The coefficient core**: two Laurent expansions (at `0`, finitely many negative powers;
at `∞`, finitely many positive powers) of one function holomorphic on `ℂ ∖ {0, 1}` and bounded
near `1` have the same coefficients. -/
theorem eq_of_glue {α β : ℤ → ℂ} {Φ : ℂ → ℂ} {n₁ m₀ : ℤ}
    (hαz : ∀ k, k < n₁ → α k = 0) (hβz : ∀ k, m₀ < k → β k = 0)
    (hA : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → HasSum (fun k : ℤ => α k * ζ ^ k) (Φ ζ))
    (hBs : ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun k : ℤ => β k * ζ ^ k) (Φ ζ))
    (hΦD : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → DifferentiableAt ℂ Φ ζ)
    {ε C : ℝ} (hε : 0 < ε) (hB : ∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < ε → ‖Φ ζ‖ ≤ C) :
    α = β := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = (-n₁).toNat := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = m₀.toNat := ⟨_, rfl⟩
  have hαneg : ∀ k : ℕ, L ≤ k → α (-((k : ℤ) + 1)) = 0 := fun k hk => hαz _ (by omega)
  have hβpos : ∀ k : ℕ, M + 1 ≤ k → β k = 0 := fun k hk => hβz _ (by omega)
  obtain ⟨Up, hUp⟩ : ∃ f : ℂ → ℂ, f = fun ζ => ∑' k : ℕ, α k * ζ ^ k := ⟨_, rfl⟩
  obtain ⟨Um, hUm⟩ : ∃ f : ℂ → ℂ,
      f = fun ζ => ∑ k ∈ Finset.range L, α (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1)) := ⟨_, rfl⟩
  obtain ⟨Vp, hVp⟩ : ∃ f : ℂ → ℂ,
      f = fun ζ => ∑ k ∈ Finset.range (M + 1), β k * ζ ^ k := ⟨_, rfl⟩
  have hsplit0 : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 →
      HasSum (fun k : ℕ => α k * ζ ^ k) (Φ ζ - Um ζ) := by
    intro ζ h0 h1
    rw [hUm]
    exact hasSum_nat_of_int L hαneg (hA ζ h0 h1)
  have hsplitI : ∀ ζ : ℂ, 1 < ‖ζ‖ →
      HasSum (fun k : ℕ => β (-((k : ℤ) + 1)) * ζ ^ (-((k : ℤ) + 1))) (Φ ζ - Vp ζ) := by
    intro ζ h1
    rw [hVp]
    exact hasSum_split_inf M hβpos (hBs ζ h1)
  -- holomorphy of the pieces
  have hUpS : ∀ q : ℂ, ‖q‖ < 1 → Summable fun k : ℕ => α k * q ^ k := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
        rw [Finset.mem_singleton] at hk
        rw [zero_pow hk, mul_zero]
    · exact (hsplit0 q hq0 hq).summable
  have hUpD : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ Up z := fun z hz => by
    rw [hUp]; exact differentiableAt_powerSeries (fun k : ℕ => α k) hUpS hz
  have hUpEq : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → Up ζ = Φ ζ - Um ζ := fun ζ h0 h1 => by
    rw [hUp]; exact (hsplit0 ζ h0 h1).tsum_eq
  have hUmD : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ Um z := by
    intro z hz
    rw [hUm]
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_const _).mul (differentiableAt_zpow.2 (Or.inl hz))
  have hVpD : ∀ z : ℂ, DifferentiableAt ℂ Vp z := by
    intro z
    rw [hVp]
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_const _).mul (differentiableAt_pow _)
  -- the auxiliary function `H`
  obtain ⟨H, hH⟩ : ∃ f : ℂ → ℂ,
      f = fun ζ => if ‖ζ‖ < 1 then Up ζ - Vp ζ else Φ ζ - Um ζ - Vp ζ := ⟨_, rfl⟩
  have hHout : ∀ ζ : ℂ, ζ ≠ 0 → H ζ = Φ ζ - Um ζ - Vp ζ := by
    intro ζ h0
    rw [hH]
    dsimp only
    split_ifs with h1
    · rw [hUpEq ζ h0 h1]
    · rfl
  have hHin : ∀ ζ : ℂ, ‖ζ‖ < 1 → H ζ = Up ζ - Vp ζ := by
    intro ζ h1
    rw [hH]
    dsimp only
    rw [if_pos h1]
  have hHD : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ H z := by
    intro z hz1
    by_cases hz : ‖z‖ < 1
    · have hev : H =ᶠ[𝓝 z] fun ζ => Up ζ - Vp ζ := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with ζ hζ
        exact hHin ζ hζ
      exact ((hUpD z hz).sub (hVpD z)).congr_of_eventuallyEq hev
    · have hz0 : z ≠ 0 := fun h => hz (by rw [h, norm_zero]; exact one_pos)
      have hev : H =ᶠ[𝓝 z] fun ζ => Φ ζ - Um ζ - Vp ζ := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with ζ hζ
        exact hHout ζ hζ
      exact (((hΦD z hz0 hz1).sub (hUmD z hz0)).sub (hVpD z)).congr_of_eventuallyEq hev
  -- boundedness near `1`
  obtain ⟨ε', hε'⟩ : ∃ e : ℝ, e = min ε (1 / 2) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min hε (by norm_num)
  have hε'1 : ε' ≤ ε := by rw [hε']; exact min_le_left _ _
  have hε'2 : ε' ≤ 1 / 2 := by rw [hε']; exact min_le_right _ _
  have hcont : ContinuousOn (fun ζ => Um ζ + Vp ζ) (Metric.closedBall (1 : ℂ) (1 / 2)) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, norm_one] at hz
      norm_num at hz
    exact ((hUmD z hz0).add (hVpD z)).continuousAt.continuousWithinAt
  obtain ⟨C', hC'⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn hcont
  have hHbdd : BddAbove (norm ∘ H '' (Metric.ball (1 : ℂ) ε' \ {1})) := by
    refine ⟨C + C', ?_⟩
    rintro _ ⟨ζ, ⟨hζb, hζ1⟩, rfl⟩
    have hζ1 : ζ ≠ 1 := hζ1
    rw [Metric.mem_ball, dist_eq_norm] at hζb
    have hζ0 : ζ ≠ 0 := by
      intro h
      rw [h, zero_sub, norm_neg, norm_one] at hζb
      linarith
    simp only [Function.comp_apply]
    rw [hHout ζ hζ0, sub_sub]
    have h1 := hB ζ hζ1 (lt_of_lt_of_le hζb hε'1)
    have h2 := hC' ζ (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_trans hζb.le hε'2)
    calc ‖Φ ζ - (Um ζ + Vp ζ)‖ ≤ ‖Φ ζ‖ + ‖Um ζ + Vp ζ‖ := norm_sub_le _ _
      _ ≤ C + C' := add_le_add h1 h2
  obtain ⟨H', hH'⟩ : ∃ f : ℂ → ℂ, f = Function.update H 1 (limUnder (𝓝[≠] (1 : ℂ)) H) :=
    ⟨_, rfl⟩
  have hH'ne : ∀ ζ : ℂ, ζ ≠ 1 → H' ζ = H ζ := fun ζ hζ => by
    rw [hH']; exact Function.update_of_ne hζ _ _
  have hH'D : Differentiable ℂ H' := by
    intro z
    by_cases hz : z = 1
    · subst hz
      have := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds (1 : ℂ) hε'0)
        (fun ζ hζ => (hHD ζ hζ.2).differentiableWithinAt) hHbdd
      rw [hH']
      exact this.differentiableAt (Metric.ball_mem_nhds (1 : ℂ) hε'0)
    · have hev : H' =ᶠ[𝓝 z] H := by
        filter_upwards [isOpen_ne.mem_nhds hz] with ζ hζ
        exact hH'ne ζ hζ
      exact (hHD z hz).congr_of_eventuallyEq hev
  -- `H` tends to `0` at infinity
  have hβ2 : Summable fun k : ℕ => ‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1) := by
    have h2 := (hsplitI 2 (by norm_num)).summable
    have h3 := (summable_norm_iff (E := ℂ)).2 h2
    refine h3.congr fun k => ?_
    rw [norm_mul, neg_succ_zpow, norm_pow, norm_inv, Complex.norm_ofNat, one_div]
  have hbound : ∀ ζ : ℂ, 2 ≤ ‖ζ‖ → ‖H ζ‖ ≤
      ((2 * ∑' k : ℕ, ‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1)) +
        ∑ k ∈ Finset.range L, ‖α (-((k : ℤ) + 1))‖) / ‖ζ‖ := by
    intro ζ hζ
    have hζ1 : 1 < ‖ζ‖ := by linarith
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ; linarith
    have hHe : H ζ = (Φ ζ - Vp ζ) - Um ζ := by rw [hHout ζ hζ0]; ring
    rw [hHe, add_div]
    refine (norm_sub_le _ _).trans (add_le_add (norm_tail_le hζ hβ2 (hsplitI ζ hζ1)) ?_)
    rw [hUm]
    exact norm_principal_le L hζ1.le
  have hlim : Tendsto H' (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun ζ : ℂ => ((2 * ∑' k : ℕ, ‖β (-((k : ℤ) + 1))‖ * (1 / 2 : ℝ) ^ (k + 1)) +
        ∑ k ∈ Finset.range L, ‖α (-((k : ℤ) + 1))‖) / ‖ζ‖) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    refine squeeze_zero_norm' ?_ h1
    have h2 : ∀ᶠ ζ : ℂ in cocompact ℂ, 2 ≤ ‖ζ‖ :=
      tendsto_norm_cocompact_atTop.eventually_ge_atTop 2
    filter_upwards [h2] with ζ hζ
    have hζ1 : ζ ≠ 1 := fun h => by rw [h, norm_one] at hζ; norm_num at hζ
    rw [hH'ne ζ hζ1]
    exact hbound ζ hζ
  have hzero : ∀ ζ : ℂ, ζ ≠ 1 → H ζ = 0 := by
    intro ζ hζ
    have := hH'D.apply_eq_of_tendsto_cocompact ζ hlim
    rwa [hH'ne ζ hζ] at this
  -- coefficients at `0`
  have hpos : ∀ k : ℕ, α k = β k := by
    have hd := coeffs_eq_zero_of_hasSum_zero' (fun k => α k - if k ≤ M then β k else 0)
      (fun q hq0 hq1 => by
        have hU := hsplit0 q hq0 hq1
        have hV : HasSum (fun k : ℕ => (if k ≤ M then β k else 0) * q ^ k) (Vp q) := by
          rw [hVp]
          refine (hasSum_sum_of_ne_finset_zero (s := Finset.range (M + 1))
            (f := fun k : ℕ => β k * q ^ k) fun k hk => ?_).congr_fun fun k => ?_
          · rw [Finset.mem_range, not_lt] at hk
            change β k * q ^ k = 0
            rw [hβpos k hk, zero_mul]
          · dsimp only
            split_ifs with h
            · rfl
            · rw [hβpos k (by omega), zero_mul]
        have hq : q ≠ 1 := fun h => by rw [h, norm_one] at hq1; exact lt_irrefl _ hq1
        have h0 := hzero q hq
        rw [hHin q hq1, hUpEq q hq0 hq1] at h0
        have h3 := hU.sub hV
        rw [h0] at h3
        refine h3.congr_fun fun k => ?_
        ring)
    intro k
    have := congrFun hd k
    simp only [Pi.zero_apply] at this
    split_ifs at this with h
    · exact sub_eq_zero.1 this
    · rw [sub_zero] at this
      rw [this, hβpos k (by omega)]
  -- coefficients at `∞`
  have hneg : ∀ k : ℕ, α (-((k : ℤ) + 1)) = β (-((k : ℤ) + 1)) := by
    have hd := coeffs_eq_zero_of_hasSum_zero'
      (fun k => β (-((k : ℤ) + 1)) - α (-((k : ℤ) + 1)))
      (fun w hw0 hw1 => by
        have hζ1 : 1 < ‖w⁻¹‖ := by
          rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 hw0)).2 hw1
        have hVms := hsplitI w⁻¹ hζ1
        have hUms : HasSum (fun k : ℕ => α (-((k : ℤ) + 1)) * w⁻¹ ^ (-((k : ℤ) + 1)))
            (Um w⁻¹) := by
          rw [hUm]
          exact hasSum_sum_of_ne_finset_zero fun k hk => by
            rw [Finset.mem_range, not_lt] at hk
            rw [hαneg k hk, zero_mul]
        have hζ1' : w⁻¹ ≠ 1 := fun h => by rw [h, norm_one] at hζ1; exact lt_irrefl _ hζ1
        have h0 := hzero w⁻¹ hζ1'
        rw [hHout w⁻¹ (inv_ne_zero hw0)] at h0
        have hdiff : (Φ w⁻¹ - Vp w⁻¹) - Um w⁻¹ = 0 := by rw [← h0]; ring
        have h2 := (hVms.sub hUms).mul_left w⁻¹
        rw [hdiff, mul_zero] at h2
        refine h2.congr_fun fun k => ?_
        rw [neg_succ_zpow, inv_inv, pow_succ]
        field_simp)
    intro k
    exact (sub_eq_zero.1 (congrFun hd k)).symm
  funext k
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact hpos n
  · cases n with
    | zero => exact hpos 0
    | succ m =>
      rw [show (-((m + 1 : ℕ) : ℤ)) = -((m : ℤ) + 1) by push_cast; ring]
      exact hneg m

variable {N : ℕ} {s t : ℤ → ℂ} {Ψ : ℂ → ℂ}

/-- **Gluing criterion.** If `Ψ` is holomorphic on `ℂ ∖ {0, 1}`, has the Laurent expansion
`Σ s n ζⁿ` on `‖ζ‖ > 1` (with `s` vanishing for large `n`) and `Σ t n ζⁿ` on `0 < ‖ζ‖ < 1` (with `t`
vanishing for small `n`), and `(ζ-1)ᴺ Ψ` is bounded near `1`, then
`(ζ - 1)ᴺ Σ s n ζⁿ = (ζ - 1)ᴺ Σ t n ζⁿ` coefficientwise. -/
theorem conv_eq_of_glue {n₀ n₁ : ℤ} (hs0 : ∀ n, n₀ < n → s n = 0) (ht0 : ∀ n, n < n₁ → t n = 0)
    (hS : ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℤ => s n * ζ ^ n) (Ψ ζ))
    (hT : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → HasSum (fun n : ℤ => t n * ζ ^ n) (Ψ ζ))
    (hΨ : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → DifferentiableAt ℂ Ψ ζ)
    {ε C : ℝ} (hε : 0 < ε) (hB : ∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < ε → ‖(ζ - 1) ^ N * Ψ ζ‖ ≤ C) :
    ∀ k : ℤ, conv N s k = conv N t k := by
  have h := eq_of_glue (α := conv N t) (β := conv N s) (Φ := fun ζ => (ζ - 1) ^ N * Ψ ζ)
    (n₁ := n₁) (m₀ := n₀ + N)
    (fun k hk => conv_eq_zero_of_lt ht0 hk) (fun k hk => conv_eq_zero_of_gt hs0 hk)
    (fun ζ h0 h1 => hasSum_conv N h0 (hT ζ h0 h1))
    (fun ζ h1 => hasSum_conv N (fun h0 => by rw [h0, norm_zero] at h1; linarith) (hS ζ h1))
    (fun ζ h0 h1 => ((differentiableAt_id.sub_const 1).pow N).mul (hΨ ζ h0 h1)) hε hB
  intro k
  exact (congrFun h k).symm

end VOA.Huang.HKLLoc
