/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelFricke
import VOA.Classification.COne.SerreStarkBoundedEigen
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# Serre–Stark S5-3 (route C3): the Hecke functional equation for θ-type forms

For a θ-type form `f` of level `N` (`24 ∣ N`) with Fricke transform `W f = fricke N f`, the pair
`x ↦ f(i x/√N)`, `x ↦ (W f)(i x/√N)` is a Mathlib `WeakFEPair` of weight `1/2` and root number
`ε_N = (√N/2)^{1/2}` (`fePair`). Consequently (Hecke):

* `fePair_Λ_eq`: for `Re s > 5/4`, `Λ(s) = Γ(s) (2π/√N)^{-s} L(s, f)` with
  `L(s, f) = Σ_{n ≥ 1} a(n) n^{-s}` (Mathlib `LSeries`), and likewise `Λ_W(s)` for `W f`;
* `fePair_functional_equation`: `Λ(1/2 − s) = ε_N Λ_W(s)` for all `s`;
* `Λ` is holomorphic away from `s ∈ {0, 1/2}` (Mathlib `WeakFEPair.differentiableAt_Λ`).

Analytic inputs: the decay `‖f(τ) − a(0)‖ ≤ K e^{−2π Im τ}` (`norm_sub_coeff_zero_le`), and the
coefficient bound `|a(n)|² ≤ C √n` (`norm_coeff_sq_le`, S5-2) for absolute convergence.
-/

open Complex Filter Topology Asymptotics Set
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Decay at `i∞` after removing the constant term -/

/-- `‖f(τ) − a(0)‖ ≤ K e^{−2π Im τ}` on `Im τ ≥ 1`. -/
theorem norm_sub_coeff_zero_le {N : ℕ} {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) :
    ∃ K : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖f τ - thetaTypeCoeff f 0‖ ≤ K * Real.exp (-(2 * Real.pi * τ.im)) := by
  have h0 : 0 < (I / 2 : ℂ).im := by simp
  have hs := (hf.hasSum_coeff h0).summable
  have hterm : ∀ n : ℕ, ‖thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * (I / 2))‖ =
      ‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have : (2 * (Real.pi : ℂ) * I * n * (I / 2)) = ((-(Real.pi * n) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, Complex.ofReal_re]
  obtain ⟨K₀, hK₀⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
  have hK₀' : ∀ n, ‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n)) ≤ K₀ := fun n => by
    rw [← hterm]; exact hK₀ ⟨n, rfl⟩
  have hK₀0 : 0 ≤ K₀ := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hK₀' 0)
  have hr0 : 0 ≤ Real.exp (-Real.pi) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  refine ⟨K₀ * Real.exp (2 * Real.pi) * (1 - Real.exp (-Real.pi))⁻¹, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ.im := by linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (K₀ * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)))
  have hfin : K₀ * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)) *
      (1 - Real.exp (-Real.pi))⁻¹ = K₀ * Real.exp (2 * Real.pi) *
      (1 - Real.exp (-Real.pi))⁻¹ * Real.exp (-(2 * Real.pi * τ.im)) := by ring
  rw [← hfin]
  have hS := (hf.hasSum_coeff hτ0).update 0 0
  have e0 : f τ - thetaTypeCoeff f 0 = 0 - thetaTypeCoeff f 0 *
      cexp (2 * Real.pi * I * ((0 : ℕ) : ℂ) * τ) + f τ := by simp; ring
  rw [e0]
  refine hS.norm_le_of_bounded hg fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Function.update_self, norm_zero]
    positivity
  · rw [Function.update_of_ne hn.ne', norm_mul, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * I * n * τ).re = -(2 * Real.pi * n * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp : Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im)) ≤
        Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)) *
          Real.exp (-Real.pi) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hnB : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hnB))
        (sub_nonneg.2 hτ)]
    have h1 : Real.exp (-(Real.pi * n)) * Real.exp (Real.pi * n) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc ‖thetaTypeCoeff f n‖ * Real.exp (-(2 * Real.pi * n * τ.im))
        = (‖thetaTypeCoeff f n‖ * Real.exp (-(Real.pi * n))) *
          (Real.exp (Real.pi * n) * Real.exp (-(2 * Real.pi * n * τ.im))) := by
          linear_combination (-(‖thetaTypeCoeff f n‖ *
            Real.exp (-(2 * Real.pi * n * τ.im)))) * h1
      _ ≤ K₀ * (Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)) *
          Real.exp (-Real.pi) ^ n) :=
          mul_le_mul (hK₀' n) hexp (by positivity) hK₀0
      _ = K₀ * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * τ.im)) *
          Real.exp (-Real.pi) ^ n := by ring

/-! ## The rescaled imaginary axis -/

/-- `x ↦ f(i x/√N)`. -/
def axisFn (N : ℕ) (f : ℂ → ℂ) (x : ℝ) : ℂ := f (I * ((x / Real.sqrt N : ℝ) : ℂ))

/-- The root number `ε_N = (√N/2)^{1/2}`. -/
def feRoot (N : ℕ) : ℂ := (((Real.sqrt N / 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

theorem feRoot_ne_zero {N : ℕ} (hN : 0 < N) : feRoot N ≠ 0 := by
  have : 0 < Real.sqrt N / 2 := by positivity
  rw [feRoot, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos this _).ne'

theorem im_axis {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 < x) :
    0 < (I * ((x / Real.sqrt N : ℝ) : ℂ)).im := by
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have : 0 < x / Real.sqrt N := by positivity
  linarith

theorem continuousOn_axisFn {N : ℕ} (hN : 0 < N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) :
    ContinuousOn (axisFn N f) (Ioi 0) := by
  have hc : Continuous fun x : ℝ => I * ((x / Real.sqrt N : ℝ) : ℂ) := by fun_prop
  refine hf.holo.continuousOn.comp hc.continuousOn fun x hx => ?_
  exact im_axis hN hx

theorem axisFn_sub_isBigO {N : ℕ} (hN : 0 < N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) (r : ℝ) :
    (fun x => axisFn N f x - thetaTypeCoeff f 0) =O[atTop] (· ^ r) := by
  obtain ⟨K, hK⟩ := norm_sub_coeff_zero_le hf
  have hsN : 0 < Real.sqrt N := by positivity
  have h1 : (fun x => axisFn N f x - thetaTypeCoeff f 0) =O[atTop]
      (fun x : ℝ => Real.exp (-(2 * Real.pi / Real.sqrt N) * x)) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_ge_atTop (Real.sqrt N)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le hsN hx
    have him : (I * ((x / Real.sqrt N : ℝ) : ℂ)).im = x / Real.sqrt N := by simp
    have h1 : 1 ≤ (I * ((x / Real.sqrt N : ℝ) : ℂ)).im := by
      rw [him, le_div_iff₀ hsN, one_mul]; exact hx
    have := hK _ h1
    rw [him] at this
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    convert this using 3
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- The Fricke transform on the rescaled axis: `f(1/x) = ε_N x^{1/2} (W f)(x)`. -/
theorem axisFn_inv {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    axisFn N f (1 / x) = (feRoot N * ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • axisFn N (fricke N f) x := by
  have hsN : 0 < Real.sqrt N := by positivity
  have hsq : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hs0 : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsN.ne'
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  rw [axisFn, axisFn, fricke_eq_cpow hN f (im_axis hN hx), smul_eq_mul]
  have e1 : (-1 / ((N : ℂ) * (I * ((x / Real.sqrt N : ℝ) : ℂ)))) =
      I * (((1 / x) / Real.sqrt N : ℝ) : ℂ) := by
    push_cast
    rw [← hsq]
    field_simp
    ring_nf
    try simp [I_sq]
  have e2 : -I * ((N : ℂ) * (I * ((x / Real.sqrt N : ℝ) : ℂ)) / 2) =
      ((Real.sqrt N / 2 * x : ℝ) : ℂ) := by
    push_cast
    rw [← hsq]
    field_simp
    ring_nf
    try simp [I_sq]
  rw [e1, e2]
  have hpos : 0 ≤ Real.sqrt N / 2 * x := by positivity
  have e3 : ((Real.sqrt N / 2 * x : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (((Real.sqrt N / 2 * x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos]; push_cast; rfl
  rw [e3, Real.mul_rpow (by positivity) hx.le, feRoot]
  have hne : (((Real.sqrt N / 2) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hx _)).ne'
  push_cast at hne ⊢
  field_simp
  rw [mul_assoc (f _), mul_div_assoc, div_self hne, mul_one]

/-! ## The weak FE pair -/

/-- The **Hecke pair** of a θ-type form: `(x ↦ f(ix/√N), x ↦ (W f)(ix/√N))`, weight `1/2`,
root number `ε_N`, constant terms `a(0)`, `b(0)`. -/
def fePair (N : ℕ) (f : ℂ → ℂ) (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f) :
    WeakFEPair ℂ where
  f := axisFn N f
  g := axisFn N (fricke N f)
  k := 1 / 2
  ε := feRoot N
  f₀ := thetaTypeCoeff f 0
  g₀ := thetaTypeCoeff (fricke N f) 0
  hf_int := (continuousOn_axisFn hN hf).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_axisFn hN (isThetaTypeForm_fricke hN h24 hf)).locallyIntegrableOn
    measurableSet_Ioi
  hk := by norm_num
  hε := feRoot_ne_zero hN
  h_feq _ hx := axisFn_inv hN f hx
  hf_top := axisFn_sub_isBigO hN hf
  hg_top := axisFn_sub_isBigO hN (isThetaTypeForm_fricke hN h24 hf)

/-! ## Mellin transform = Dirichlet series -/

/-- The frequency scale `2π/√N`. -/
def feScale (N : ℕ) : ℝ := 2 * Real.pi / Real.sqrt N

theorem feScale_pos {N : ℕ} (hN : 0 < N) : 0 < feScale N := by
  unfold feScale; positivity

/-- `‖a(n)‖ ≤ (1 + C) n^{1/2}` for `n ≥ 4`. -/
theorem exists_norm_coeff_le {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 4 ≤ n →
      ‖thetaTypeCoeff f n‖ ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := norm_coeff_sq_le h4 hN hf
  refine ⟨1 + C, by linarith, fun n hn => ?_⟩
  have h := hC n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  rw [← Real.sqrt_eq_rpow]
  have ha := norm_nonneg (thetaTypeCoeff f n)
  nlinarith [mul_nonneg hC0 (sub_nonneg.2 hs1)]

theorem summable_norm_coeff_div {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) {σ : ℝ} (hσ : 3 / 2 < σ) :
    Summable fun n : ℕ => ‖(if n = 0 then 0 else thetaTypeCoeff f n)‖ /
      (feScale N * n) ^ σ := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_coeff_le h4 hN hf
  have hc := feScale_pos hN
  have hg : Summable fun n : ℕ => B * feScale N ^ (-σ) * (n : ℝ) ^ (1 / 2 - σ) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [if_neg (by omega), Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.mul_rpow hc.le hn0.le, Real.rpow_neg hc.le, Real.rpow_sub hn0]
  have hcs : 0 < feScale N ^ σ := Real.rpow_pos_of_pos hc σ
  have hns : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
  rw [div_le_iff₀ (mul_pos hcs hns)]
  have := hB n hn
  calc ‖thetaTypeCoeff f n‖ ≤ B * (n : ℝ) ^ (1 / 2 : ℝ) := this
    _ = B * (feScale N ^ σ)⁻¹ * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ σ) *
        (feScale N ^ σ * (n : ℝ) ^ σ) := by field_simp

/-- **Mellin = Dirichlet.** For `Re s > 3/2`,
`∫₀^∞ (f(ix/√N) − a(0)) x^{s−1} dx = Γ(s) (2π/√N)^{−s} L(s, f)`. -/
theorem mellin_axisFn {N : ℕ} (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) {s : ℂ} (hs : 3 / 2 < s.re) :
    mellin (fun x => axisFn N f x - thetaTypeCoeff f 0) s =
      Gamma s * ((feScale N : ℝ) : ℂ) ^ (-s) * LSeries (thetaTypeCoeff f) s := by
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else thetaTypeCoeff f n with ha
  set q : ℕ → ℝ := fun n => feScale N * n with hq
  have hc := feScale_pos hN
  have hp : ∀ n, a n = 0 ∨ 0 < q n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · left; simp [ha, h]
    · right; simp only [hq]; exact mul_pos hc (by exact_mod_cast h)
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n => a n * Real.exp (-q n * t))
      (axisFn N f t - thetaTypeCoeff f 0) := by
    intro t ht
    have hS := (hf.hasSum_coeff (im_axis hN ht)).update 0 0
    have e0 : axisFn N f t - thetaTypeCoeff f 0 = 0 - thetaTypeCoeff f 0 *
        cexp (2 * Real.pi * I * ((0 : ℕ) : ℂ) * (I * ((t / Real.sqrt N : ℝ) : ℂ))) +
          f (I * ((t / Real.sqrt N : ℝ) : ℂ)) := by simp [axisFn]; ring
    rw [e0]
    convert hS using 1
    funext n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha]
    · rw [Function.update_of_ne h.ne']
      simp only [ha, if_neg h.ne', hq, feScale]
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
  have hsum := summable_norm_coeff_div h4 hN hf hs
  have hM := hasSum_mellin hp (by linarith) hF (by simpa [ha, hq] using hsum)
  rw [← hM.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [ha, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero h.ne']
    simp only [ha, if_neg h.ne', hq]
    rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hc.le (Nat.cast_nonneg _), cpow_neg]
    have h1 : ((feScale N : ℝ) : ℂ) ^ s ≠ 0 :=
      cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hc.ne'))
    push_cast
    field_simp

/-! ## The functional equation -/

variable {N : ℕ} {f : ℂ → ℂ}

/-- `Λ(s) = Γ(s) (2π/√N)^{−s} L(s, f)` for `Re s > 3/2`. -/
theorem fePair_Λ_eq (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    (fePair N f hN h24 hf).Λ s =
      Gamma s * ((feScale N : ℝ) : ℂ) ^ (-s) * LSeries (thetaTypeCoeff f) s := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hk : (fePair N f hN h24 hf).k < s.re := by
    change (1 / 2 : ℝ) < s.re; linarith
  rw [← mellin_axisFn h4 hN hf hs]
  exact ((fePair N f hN h24 hf).hasMellin hk).2.symm

/-- `Λ_W(s) = Γ(s) (2π/√N)^{−s} L(s, W f)` for `Re s > 3/2`. -/
theorem fePair_symm_Λ_eq (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    (fePair N f hN h24 hf).symm.Λ s =
      Gamma s * ((feScale N : ℝ) : ℂ) ^ (-s) * LSeries (thetaTypeCoeff (fricke N f)) s := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hk : (fePair N f hN h24 hf).symm.k < s.re := by
    change (1 / 2 : ℝ) < s.re; linarith
  rw [← mellin_axisFn h4 hN (isThetaTypeForm_fricke hN h24 hf) hs]
  exact ((fePair N f hN h24 hf).symm.hasMellin hk).2.symm

/-- **Hecke's functional equation** for θ-type forms: `Λ(1/2 − s) = ε_N Λ_W(s)`. -/
theorem fePair_functional_equation (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f)
    (s : ℂ) :
    (fePair N f hN h24 hf).Λ (1 / 2 - s) = feRoot N * (fePair N f hN h24 hf).symm.Λ s := by
  have := (fePair N f hN h24 hf).functional_equation s
  have hk : (((fePair N f hN h24 hf).k : ℝ) : ℂ) = 1 / 2 := by
    change (((1 / 2 : ℝ)) : ℂ) = 1 / 2; push_cast; ring
  rw [hk] at this
  exact this

/-- `Λ` is holomorphic away from `0` and `1/2`. -/
theorem fePair_differentiableAt (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f)
    {s : ℂ} (h0 : s ≠ 0) (h12 : s ≠ 1 / 2) :
    DifferentiableAt ℂ (fePair N f hN h24 hf).Λ s := by
  refine (fePair N f hN h24 hf).differentiableAt_Λ (Or.inl h0) (Or.inl ?_)
  change s ≠ (((1 / 2 : ℝ)) : ℂ); push_cast; exact h12

/-- `Λ_W` is holomorphic away from `0` and `1/2`. -/
theorem fePair_symm_differentiableAt (hN : 0 < N) (h24 : 24 ∣ N) (hf : IsThetaTypeForm N f)
    {s : ℂ} (h0 : s ≠ 0) (h12 : s ≠ 1 / 2) :
    DifferentiableAt ℂ (fePair N f hN h24 hf).symm.Λ s := by
  refine (fePair N f hN h24 hf).symm.differentiableAt_Λ (Or.inl h0) (Or.inl ?_)
  change s ≠ (((1 / 2 : ℝ)) : ℂ); push_cast; exact h12

end SSHecke

end VOA.Classification.COne
