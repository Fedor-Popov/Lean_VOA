/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGammaZeroBridge
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Genus zero on the abstract interface: analytic basics

Analytic leaves of the genus-zero theorem (blueprint `Notes/moonshine/MOON_M8_LEAN.md`). Every
`q`-series
`f = q⁻¹ + Σ_{n ≥ 0} c (n+1) q^{n+1}` whose coefficients are dominated by those of
`J = j − 744` (`IsJDominated c`) is

* holomorphic on `ℍ` (`mdifferentiable_qSeriesFun`), with
  `‖f τ − q⁻¹‖ ≤ jTail (Im τ)` (`norm_qSeriesFun_sub_inv_qPar_le`) and `jTail y → 0`, so
  `f − q⁻¹ → 0` at `i∞` (`tendsto_qSeriesFun_sub_inv_qPar`): these are the `holomorphic` and
  `normalized` fields of `IsNormalizedHauptmodul`;
* injective modulo `ℤ` high up, at a height `t` that depends only on `J`
  (`exists_height_injective`): `f σ = f τ` with `Im σ, Im τ ≥ t` forces `σ − τ ∈ ℤ`.

The proof of the last point is a Lipschitz estimate for `q ↦ f − q⁻¹` on a small disc
(`norm_qTailSeries_sub_le`) against `‖p⁻¹ − q⁻¹‖ = ‖q − p‖ / (‖p‖ ‖q‖)`; no Faber identity is used.

Every member of a `ReplicableFamily` is `J`-dominated (`ReplicableFamily.isJDominated`), and the
family is constant on residue classes of the replicate index (`ReplicableFamily.c_eq_of_modEq`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology
open scoped Real MatrixGroups Manifold

local notation "𝕢" => Function.Periodic.qParam

/-! ### The majorant series of `J` -/

/-- The majorant coefficients `‖[q^{n+1}] J‖ = ‖[q^{n+2}] JShift‖`, `n ≥ 0`. -/
noncomputable def jCoeffMajorant (n : ℕ) : ℝ := ‖PowerSeries.coeff (n + 1 + 1) JShift‖

lemma jCoeffMajorant_nonneg (n : ℕ) : 0 ≤ jCoeffMajorant n := norm_nonneg _

/-- The coefficients of a power series that converges at `z` are dominated by a geometric
sequence at every smaller radius. -/
lemma summable_norm_mul_pow_of_summable {a : ℕ → ℂ} {z : ℂ}
    (hs : Summable fun n => a n * z ^ n) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ‖z‖) :
    Summable fun n => ‖a n‖ * r ^ n := by
  have hz : 0 < ‖z‖ := hr0.trans_lt hr
  obtain ⟨C, hC⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
  have hb : ∀ n, ‖a n‖ * r ^ n ≤ C * (r / ‖z‖) ^ n := by
    intro n
    have h1 : ‖a n * z ^ n‖ ≤ C := hC ⟨n, rfl⟩
    rw [norm_mul, norm_pow] at h1
    have h2 : ‖a n‖ * r ^ n = ‖a n‖ * ‖z‖ ^ n * (r / ‖z‖) ^ n := by
      rw [div_pow]
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (div_nonneg hr0 hz.le) n)
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)) hb
    ((summable_geometric_of_lt_one (div_nonneg hr0 hz.le) ((div_lt_one hz).mpr hr)).mul_left C)

lemma norm_qPar_eq (τ : ℍ) : ‖qPar τ‖ = Real.exp (-2 * π * τ.im) := by
  rw [qPar, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]

lemma real_exp_mul_succ (x : ℝ) (n : ℕ) :
    Real.exp (x * (n + 1)) = Real.exp x ^ (n + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The majorant series converges**: `Σ ‖[q^{n+1}] J‖ e^{−2π(n+1)y} < ∞` for `y > 0`. -/
lemma summable_jCoeffMajorant_mul_exp {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * y) := by
  set z : ℍ := ⟨((y / 2 : ℝ) : ℂ) * Complex.I, by simpa using half_pos hy⟩ with hzdef
  set q₀ : ℂ := 𝕢 1 (z : ℂ) with hq₀
  have hzim : (z : ℂ).im = y / 2 := by simp [hzdef]
  have hq₀n : ‖q₀‖ = Real.exp (-2 * π * (y / 2)) := by
    rw [hq₀, Function.Periodic.norm_qParam, div_one, hzim]
  have hs0 : Summable fun n : ℕ => PowerSeries.coeff (n + 1) JShift * q₀ ^ n :=
    (hasSum_JShift_laurent z).summable
  have hs1 : Summable fun n : ℕ => (PowerSeries.coeff (n + 1 + 1) JShift * q₀) * q₀ ^ n := by
    refine ((summable_nat_add_iff 1).mpr hs0).congr fun n => ?_
    simp only [pow_succ]
    ring
  set r : ℝ := Real.exp (-2 * π * y) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrq : r < ‖q₀‖ := by
    rw [hq₀n, hr, Real.exp_lt_exp]
    nlinarith [Real.pi_pos]
  have hq₀pos : 0 < ‖q₀‖ := hr0.trans_lt hrq
  refine ((summable_norm_mul_pow_of_summable hs1 hr0 hrq).mul_right (r / ‖q₀‖)).congr
    fun n => ?_
  rw [norm_mul, jCoeffMajorant]
  have he : Real.exp (-2 * π * (n + 1) * y) = r ^ (n + 1) := by
    rw [hr, ← real_exp_mul_succ]
    congr 1
    ring
  rw [he, pow_succ]
  field_simp

/-! ### The tail function -/

/-- `jTail y = Σ_{n ≥ 0} ‖[q^{n+1}] J‖ e^{−2π(n+1)y}`: bounds `‖f τ − q⁻¹‖` at height `y`. -/
noncomputable def jTail (y : ℝ) : ℝ :=
  ∑' n : ℕ, jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * y)

lemma jTail_nonneg (y : ℝ) : 0 ≤ jTail y :=
  tsum_nonneg fun n => mul_nonneg (jCoeffMajorant_nonneg n) (Real.exp_pos _).le

lemma exp_neg_mul_le_of_le {y y' : ℝ} (hyy : y ≤ y') (n : ℕ) :
    Real.exp (-2 * π * (n + 1) * y') ≤ Real.exp (-2 * π * (n + 1) * y) := by
  refine Real.exp_le_exp.mpr ?_
  have h0 : (0 : ℝ) ≤ 2 * π * (n + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hyy h0]

lemma jTail_le_of_le {y y' : ℝ} (hy : 0 < y) (hyy : y ≤ y') : jTail y' ≤ jTail y :=
  (summable_jCoeffMajorant_mul_exp (hy.trans_le hyy)).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (exp_neg_mul_le_of_le hyy n) (jCoeffMajorant_nonneg n))
    (summable_jCoeffMajorant_mul_exp hy)

/-- `jTail y → 0` as `y → ∞` (dominated convergence for series). -/
lemma tendsto_jTail_atTop : Tendsto jTail atTop (𝓝 0) := by
  have hterm : ∀ n : ℕ, Tendsto (fun y : ℝ => jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * y))
      atTop (𝓝 0) := by
    intro n
    have h1 : Tendsto (fun y : ℝ => (2 * π * (n + 1)) * y) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have h3 : Tendsto (fun y : ℝ => Real.exp (-2 * π * (n + 1) * y)) atTop (𝓝 0) := by
      refine h2.congr fun y => ?_
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa using h3.const_mul (jCoeffMajorant n)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (y : ℝ) (n : ℕ) => jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * y))
    (g := fun _ => (0 : ℝ)) (summable_jCoeffMajorant_mul_exp one_pos) hterm (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy n
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (jCoeffMajorant_nonneg n) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (exp_neg_mul_le_of_le hy n) (jCoeffMajorant_nonneg n))
  rw [tsum_zero] at h
  exact h

/-! ### `J`-dominated `q`-series -/

/-- The coefficients `c (n+1)` are dominated by those of `J`. -/
def IsJDominated (c : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ‖c (n + 1)‖ ≤ jCoeffMajorant n

/-- The regular part `Σ_{n ≥ 0} c (n+1) q^{n+1}` of a `q`-series. -/
noncomputable def qTailSeries (c : ℕ → ℂ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, c (n + 1) * q ^ (n + 1)

lemma qSeriesFun_eq_inv_add_qTailSeries (c : ℕ → ℂ) (τ : ℍ) :
    qSeriesFun c τ = (qPar τ)⁻¹ + qTailSeries c (qPar τ) :=
  rfl

lemma norm_qTail_term_le {c : ℕ → ℂ} (hc : IsJDominated c) {q : ℂ} {y : ℝ}
    (hq : ‖q‖ ≤ Real.exp (-2 * π * y)) (n : ℕ) :
    ‖c (n + 1) * q ^ (n + 1)‖ ≤ jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * y) := by
  rw [norm_mul, norm_pow]
  have h : Real.exp (-2 * π * (n + 1) * y) = Real.exp (-2 * π * y) ^ (n + 1) := by
    rw [← real_exp_mul_succ]
    congr 1
    ring
  rw [h]
  exact mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg _) hq _) (by positivity)
    (jCoeffMajorant_nonneg n)

lemma summable_qTail_term {c : ℕ → ℂ} (hc : IsJDominated c) {q : ℂ} {y : ℝ} (hy : 0 < y)
    (hq : ‖q‖ ≤ Real.exp (-2 * π * y)) :
    Summable fun n : ℕ => c (n + 1) * q ^ (n + 1) :=
  Summable.of_norm_bounded (summable_jCoeffMajorant_mul_exp hy) (norm_qTail_term_le hc hq)

lemma norm_qTailSeries_le {c : ℕ → ℂ} (hc : IsJDominated c) {q : ℂ} {y : ℝ} (hy : 0 < y)
    (hq : ‖q‖ ≤ Real.exp (-2 * π * y)) :
    ‖qTailSeries c q‖ ≤ jTail y :=
  tsum_of_norm_bounded (summable_jCoeffMajorant_mul_exp hy).hasSum (norm_qTail_term_le hc hq)

/-- **Growth at height `Im τ`**: `‖f τ − q⁻¹‖ ≤ jTail (Im τ)`. -/
theorem norm_qSeriesFun_sub_inv_qPar_le {c : ℕ → ℂ} (hc : IsJDominated c) (τ : ℍ) :
    ‖qSeriesFun c τ - (qPar τ)⁻¹‖ ≤ jTail τ.im := by
  rw [qSeriesFun_eq_inv_add_qTailSeries, add_sub_cancel_left]
  exact norm_qTailSeries_le hc τ.im_pos (norm_qPar_eq τ).le

/-- **Normalisation** (`f − q⁻¹ → 0` at `i∞`): the `normalized` field. -/
theorem tendsto_qSeriesFun_sub_inv_qPar {c : ℕ → ℂ} (hc : IsJDominated c) :
    Tendsto (fun τ : ℍ => qSeriesFun c τ - (qPar τ)⁻¹) atImInfty (𝓝 0) :=
  squeeze_zero_norm (norm_qSeriesFun_sub_inv_qPar_le hc)
    (tendsto_jTail_atTop.comp (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop))

/-- **Holomorphy**: the `holomorphic` field. -/
theorem mdifferentiable_qSeriesFun {c : ℕ → ℂ} (hc : IsJDominated c) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qSeriesFun c) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set U : Set ℂ := {w : ℂ | z.im / 2 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    simp only [hU, Set.mem_setOf_eq]
    linarith
  have hq : Differentiable ℂ (fun w : ℂ => 𝕢 1 w) := by
    unfold Function.Periodic.qParam
    fun_prop
  have hqU : ∀ w ∈ U, ‖𝕢 1 w‖ ≤ Real.exp (-2 * π * (z.im / 2)) := by
    intro w hw
    rw [Function.Periodic.norm_qParam, div_one, Real.exp_le_exp]
    have hw' : z.im / 2 < w.im := hw
    nlinarith [Real.pi_pos]
  have hT : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, c (n + 1) * 𝕢 1 w ^ (n + 1)) U :=
    Complex.differentiableOn_tsum_of_summable_norm (F :=fun n w => c (n + 1) * 𝕢 1 w ^ (n + 1))
      (summable_jCoeffMajorant_mul_exp (half_pos hz'))
      (fun n => ((hq.pow (n + 1)).const_mul (c (n + 1))).differentiableOn) hUo
      (fun n w hw => norm_qTail_term_le hc (hqU w hw) n)
  have hI : DifferentiableOn ℂ (fun w : ℂ => (𝕢 1 w)⁻¹) U :=
    hq.differentiableOn.inv fun w _ => Function.Periodic.qParam_ne_zero w
  have hD : DifferentiableAt ℂ
      (fun w : ℂ => (𝕢 1 w)⁻¹ + ∑' n : ℕ, c (n + 1) * 𝕢 1 w ^ (n + 1)) z :=
    (hI.add hT).differentiableAt (hUo.mem_nhds hzU)
  refine (hD.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  rfl

/-! ### Injectivity modulo `ℤ` high up -/

lemma norm_pow_sub_pow_le_of_norm_le {x y : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r)
    (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ n * r ^ (n - 1) * ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  calc ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖
      ≤ ∑ _i ∈ Finset.range n, r ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow, norm_pow]
        have hi' : i + (n - 1 - i) = n - 1 := by
          have := Finset.mem_range.mp hi
          omega
        calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) ≤ r ^ i * r ^ (n - 1 - i) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _)
                (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)
          _ = r ^ (n - 1) := by rw [← pow_add, hi']
    _ = n * r ^ (n - 1) := by simp

/-- **Lipschitz bound** for the regular part on a disc of radius `r ≤ 1`. -/
lemma norm_qTailSeries_sub_le {c : ℕ → ℂ} (hc : IsJDominated c) {r : ℝ} (hr1 : r ≤ 1)
    (hL : Summable fun n : ℕ => (n + 1) * jCoeffMajorant n * r ^ n) {p q : ℂ}
    (hp : ‖p‖ ≤ r) (hq : ‖q‖ ≤ r) :
    ‖qTailSeries c q - qTailSeries c p‖ ≤
      (∑' n : ℕ, (n + 1) * jCoeffMajorant n * r ^ n) * ‖q - p‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hp
  have hterm : ∀ {x : ℂ}, ‖x‖ ≤ r → ∀ n : ℕ,
      ‖c (n + 1) * x ^ (n + 1)‖ ≤ (n + 1) * jCoeffMajorant n * r ^ n := by
    intro x hx n
    rw [norm_mul, norm_pow]
    have ha := jCoeffMajorant_nonneg n
    have hrn := pow_nonneg hr0 n
    calc ‖c (n + 1)‖ * ‖x‖ ^ (n + 1) ≤ jCoeffMajorant n * r ^ (n + 1) :=
          mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity) ha
      _ ≤ (n + 1) * jCoeffMajorant n * r ^ n := by
          rw [pow_succ]
          have h1 : r ^ n * r ≤ r ^ n := by nlinarith
          have h2 : (0 : ℝ) ≤ n := n.cast_nonneg
          nlinarith [mul_nonneg ha hrn, mul_le_mul_of_nonneg_left h1 ha]
  have hsq := Summable.of_norm_bounded hL (hterm hq)
  have hsp := Summable.of_norm_bounded hL (hterm hp)
  rw [qTailSeries, qTailSeries, ← hsq.tsum_sub hsp, ← tsum_mul_right]
  refine tsum_of_norm_bounded (hL.mul_right ‖q - p‖).hasSum fun n => ?_
  rw [← mul_sub, norm_mul]
  have hpow := norm_pow_sub_pow_le_of_norm_le hq hp (n + 1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hpow
  calc ‖c (n + 1)‖ * ‖q ^ (n + 1) - p ^ (n + 1)‖
      ≤ jCoeffMajorant n * ((n + 1) * r ^ n * ‖q - p‖) :=
        mul_le_mul (hc n) hpow (norm_nonneg _) (jCoeffMajorant_nonneg n)
    _ = (n + 1) * jCoeffMajorant n * r ^ n * ‖q - p‖ := by ring

/-- The Lipschitz series converges at radius `e^{−4π}`. -/
lemma summable_lipschitz_majorant :
    Summable fun n : ℕ => (n + 1) * jCoeffMajorant n * Real.exp (-(4 * π)) ^ n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (by positivity)
      (jCoeffMajorant_nonneg n)) (pow_nonneg (Real.exp_pos _).le n)) (fun n => ?_)
    ((summable_jCoeffMajorant_mul_exp one_pos).mul_left (Real.exp (2 * π)))
  have ha := jCoeffMajorant_nonneg n
  have e1 : Real.exp (-(4 * π)) ^ n = Real.exp (n * (-(4 * π))) := (Real.exp_nat_mul _ n).symm
  have e2 : Real.exp (2 * π) * (jCoeffMajorant n * Real.exp (-2 * π * (n + 1) * 1)) =
      jCoeffMajorant n * (Real.exp (n * (2 * π)) * Real.exp (n * (-(4 * π)))) := by
    rw [← Real.exp_add, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have e3 : (n : ℝ) + 1 ≤ Real.exp (n * (2 * π)) := by
    have h := Real.add_one_le_exp (n * (2 * π))
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith [Real.pi_gt_three]
  rw [e1, e2]
  have hE := (Real.exp_pos (n * (-(4 * π)))).le
  nlinarith [mul_le_mul_of_nonneg_right e3 (mul_nonneg ha hE)]

/-- **Injectivity modulo `ℤ` high up** (uniform over all `J`-dominated series): there is a
height `t > 0` such that `f σ = f τ` with `Im σ, Im τ ≥ t` forces `σ − τ ∈ ℤ`. -/
theorem exists_height_injective :
    ∃ t : ℝ, 0 < t ∧ ∀ c : ℕ → ℂ, IsJDominated c → ∀ σ τ : ℍ, t ≤ σ.im → t ≤ τ.im →
      qSeriesFun c σ = qSeriesFun c τ → ∃ k : ℤ, (σ : ℂ) = τ + k := by
  set r₀ : ℝ := Real.exp (-(4 * π)) with hr₀
  have hr₀1 : r₀ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  set L : ℝ := ∑' n : ℕ, (n + 1) * jCoeffMajorant n * r₀ ^ n with hLdef
  have hL0 : 0 ≤ L := tsum_nonneg fun n => mul_nonneg (mul_nonneg (by positivity)
    (jCoeffMajorant_nonneg n)) (pow_nonneg (Real.exp_pos _).le n)
  set T : ℝ := max 2 (L + 1) with hT
  have hT2 : 2 ≤ T := le_max_left _ _
  have hTL : L + 1 ≤ T := le_max_right _ _
  refine ⟨T, by linarith, ?_⟩
  intro c hc σ τ hσ hτ heq
  set r : ℝ := Real.exp (-2 * π * T) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrr₀ : r ≤ r₀ := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hr1 : r ≤ 1 := hrr₀.trans hr₀1
  have hrL : r * L < 1 := by
    have hexp : L < Real.exp (2 * π * T) := by
      have h := Real.add_one_le_exp (2 * π * T)
      nlinarith [Real.pi_gt_three]
    have hone : r * Real.exp (2 * π * T) = 1 := by
      rw [hr, ← Real.exp_add]
      simp
    nlinarith [Real.exp_pos (-2 * π * T)]
  have hσr : ‖qPar σ‖ ≤ r := by
    rw [norm_qPar_eq, hr, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have hτr : ‖qPar τ‖ ≤ r := by
    rw [norm_qPar_eq, hr, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  set p := qPar σ with hp
  set q := qPar τ with hq
  have hpq : p = q := by
    by_contra hne
    have hp0 : p ≠ 0 := Function.Periodic.qParam_ne_zero _
    have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero _
    rw [qSeriesFun_eq_inv_add_qTailSeries, qSeriesFun_eq_inv_add_qTailSeries] at heq
    have h1 : p⁻¹ - q⁻¹ = qTailSeries c q - qTailSeries c p := by
      linear_combination heq
    have h2 : ‖p⁻¹ - q⁻¹‖ = ‖q - p‖ / (‖p‖ * ‖q‖) := by
      rw [inv_sub_inv hp0 hq0, norm_div, norm_mul]
    have h3 := norm_qTailSeries_sub_le hc hr₀1 summable_lipschitz_majorant
      (hσr.trans hrr₀) (hτr.trans hrr₀)
    rw [← hLdef, ← h1, h2] at h3
    have hqp : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hpp : 0 < ‖p‖ * ‖q‖ := mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hq0)
    have h4 : ‖q - p‖ ≤ L * ‖q - p‖ * (‖p‖ * ‖q‖) := (div_le_iff₀ hpp).mp h3
    have h5 : ‖q - p‖ * 1 ≤ ‖q - p‖ * (L * (‖p‖ * ‖q‖)) := by
      linarith [show L * ‖q - p‖ * (‖p‖ * ‖q‖) = ‖q - p‖ * (L * (‖p‖ * ‖q‖)) by ring]
    have h6 : 1 ≤ L * (‖p‖ * ‖q‖) := le_of_mul_le_mul_left h5 hqp
    have h7 : L * (‖p‖ * ‖q‖) ≤ L * (r * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hσr hτr (norm_nonneg _) hr0) hL0
    have h8 : L * (r * r) ≤ L * r :=
      mul_le_mul_of_nonneg_left (by nlinarith) hL0
    linarith [mul_comm r L]
  have hexp : Complex.exp (2 * π * Complex.I * (σ : ℂ) / 1) =
      Complex.exp (2 * π * Complex.I * (τ : ℂ) / 1) := hpq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨n, mul_left_cancel₀ h2pi ?_⟩
  rw [div_one, div_one] at hn
  linear_combination hn

/-! ### Replicable families -/

namespace ReplicableFamily

variable {N : ℕ} (F : ReplicableFamily N)

/-- Every member of a replicable family is dominated by `J`. -/
lemma isJDominated (k : ℕ) : IsJDominated (F.c k) := fun n => by
  have h := F.dominated k (n + 1)
  rwa [F.zero_eq_J (n + 1)] at h

/-- The `holomorphic` field for every member. -/
lemma mdifferentiable (k : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qSeriesFun (F.c k)) :=
  mdifferentiable_qSeriesFun (F.isJDominated k)

/-- The `normalized` field for every member. -/
lemma tendsto_sub_inv_qPar (k : ℕ) :
    Tendsto (fun τ : ℍ => qSeriesFun (F.c k) τ - (qPar τ)⁻¹) atImInfty (𝓝 0) :=
  tendsto_qSeriesFun_sub_inv_qPar (F.isJDominated k)

lemma c_add_mul (k m : ℕ) : F.c (k + N * m) = F.c k := by
  induction m with
  | zero => simp
  | succ m ih =>
    funext n
    rw [mul_add_one, ← add_assoc, F.periodic, ih]

/-- Replicates depend only on the residue of the index modulo the period. -/
lemma c_eq_of_modEq {k k' : ℕ} (h : k ≡ k' [MOD N]) : F.c k = F.c k' := by
  rcases le_total k k' with hk | hk
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hk).mp h
    have hk' : k' = k + N * m := by
      rw [← hm]
      omega
    rw [hk', F.c_add_mul]
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hk).mp h.symm
    have hk' : k = k' + N * m := by
      rw [← hm]
      omega
    rw [hk', F.c_add_mul]

/-- For an admissible prime (or any `u ≡ 1 mod N`) the replicate `k * u` equals `k`. -/
lemma c_mul_eq_of_modEq_one {u : ℕ} (hu : u ≡ 1 [MOD N]) (k : ℕ) : F.c (k * u) = F.c k := by
  refine F.c_eq_of_modEq ?_
  simpa using Nat.ModEq.mul_left k hu

end ReplicableFamily

end VOA.Moonshine.ConwayNorton
