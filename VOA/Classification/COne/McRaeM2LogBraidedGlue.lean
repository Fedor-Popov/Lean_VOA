import VOA.Huang.HexagonCloseGeom
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Gluing four expansions around the equilateral configuration (VOA-free)

Abstract form of the hexagon gluing in the coordinate `u` (`x` at `1+u`, `y` at `1`,
`z` at `0`), for a sign `s = ±1` selecting the half plane `s·Im u > 0`. Four
functions are given: `fA` (holomorphic on `|1+u| > 1`), `fC` (on `|1+u| < 1`,
`s·Im u > 0`), `fD` (on `|u| < |1+u|`) and a half-plane function `Φ` (on
`s·Im u > 0`), with `fA = Φ` near `u = -3 + 2si`, `fC = Φ` near `u = -3/4`
and `fC = fD` near `u = -1/4`. Then `fA = fD` on `Re u > 0`
(`glue_four`). The three agreements are local; the half-plane function crosses
the equilateral configuration `u = e^{∓2πi/3}`, where none of the other three
expansions converges. -/
noncomputable section
namespace VOA.Huang.LogBraided
open Complex Filter Topology
open VOA.Huang.TensorCat.HexagonClose (sign_cases)

/-- The identity theorem on a convex open set, from an open nonempty piece. -/
theorem eqOn_of_convex_open {f g : ℂ → ℂ} {U O : Set ℂ} (hUc : Convex ℝ U) (hU : IsOpen U)
    (hf : ∀ u ∈ U, DifferentiableAt ℂ f u) (hg : ∀ u ∈ U, DifferentiableAt ℂ g u)
    (hO : IsOpen O) (hOU : O ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ O) (hfg : Set.EqOn f g O) :
    Set.EqOn f g U := by
  have hfa : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun u hu => (hf u hu).differentiableWithinAt) hU
  have hga : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun u hu => (hg u hu).differentiableWithinAt) hU
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc.isPreconnected (hOU hz₀)
    (Filter.eventuallyEq_of_mem (hO.mem_nhds hz₀) hfg)

theorem convex_sim_gt' (s a : ℝ) : Convex ℝ {r : ℂ | a < s * r.im} :=
  convex_halfSpace_gt (f := fun r : ℂ => s * r.im)
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩ a

theorem convex_re_gt' (a : ℝ) : Convex ℝ {r : ℂ | a < r.re} := convex_halfSpace_re_gt a

theorem isOpen_sim_gt' (s a : ℝ) : IsOpen {r : ℂ | a < s * r.im} :=
  isOpen_lt continuous_const (continuous_const.mul continuous_im)

theorem isOpen_re_gt' (a : ℝ) : IsOpen {r : ℂ | a < r.re} :=
  isOpen_lt continuous_const continuous_re

theorem isOpen_re_lt' (a : ℝ) : IsOpen {r : ℂ | r.re < a} :=
  isOpen_lt continuous_re continuous_const

theorem mem_slitPlane_of_sim' {s : ℝ} {z : ℂ} (h : 0 < s * z.im) : z ∈ Complex.slitPlane := by
  refine Or.inr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

theorem point_mem' (s : ℝ) (hs : s = 1 ∨ s = -1) (a b : ℝ) :
    ((a : ℂ) + ((b * s : ℝ) : ℂ) * Complex.I).re = a ∧
      s * ((a : ℂ) + ((b * s : ℝ) : ℂ) * Complex.I).im = b := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  constructor
  · ring
  · have := sign_cases hs
    linear_combination b * this

theorem one_lt_norm_one_add_of_sim' {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ}
    (hr : 1 < s * r.im) : 1 < ‖1 + r‖ := by
  have h1 := Complex.abs_im_le_norm (1 + r)
  have h2 : s * r.im ≤ |(1 + r).im| := by
    simp only [Complex.add_im, Complex.one_im, zero_add]
    rcases hs with rfl | rfl
    · simpa using le_abs_self r.im
    · have := neg_abs_le r.im
      simp only [neg_mul, one_mul]
      linarith
  linarith

theorem normSq_one_add_sub' (r : ℂ) :
    Complex.normSq (1 + r) - Complex.normSq r = 1 + 2 * r.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
    Complex.one_im]
  ring

theorem norm_lt_norm_one_add' {r : ℂ} (h : -1 / 2 < r.re) : ‖r‖ < ‖1 + r‖ := by
  have h1 := normSq_one_add_sub' r
  have h2 : Complex.normSq r < Complex.normSq (1 + r) := by linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

theorem norm_one_add_lt_norm' {r : ℂ} (h : r.re < -1 / 2) : ‖1 + r‖ < ‖r‖ := by
  have h1 := normSq_one_add_sub' r
  have h2 : Complex.normSq (1 + r) < Complex.normSq r := by linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

/-- **The gluing theorem** (VOA-free). -/
theorem glue_four {s : ℝ} (hs : s = 1 ∨ s = -1) (fA fC fD Φ : ℂ → ℂ)
    (hA : ∀ u, 1 < ‖1+u‖ → 1+u ∈ Complex.slitPlane → DifferentiableAt ℂ fA u)
    (hC : ∀ u, ‖1+u‖ < 1 → 0 < s*u.im → DifferentiableAt ℂ fC u)
    (hD : ∀ u, ‖u‖ < ‖1+u‖ → u ∈ Complex.slitPlane → 1+u ∈ Complex.slitPlane →
      DifferentiableAt ℂ fD u)
    (hΦ : ∀ u, 0 < s*u.im → DifferentiableAt ℂ Φ u)
    (hAΦ : ∀ u, u.re < -2 → 1 < s*u.im → fA u = Φ u)
    (hCΦ : ∀ u ∈ Metric.ball (-3/4 : ℂ) (1/4), 0 < s*u.im → fC u = Φ u)
    (hCD : ∀ u ∈ Metric.ball (-1/2 : ℂ) (1/2), -1/2 < u.re → 0 < s*u.im → fC u = fD u) :
    ∀ u, 0 < u.re → fA u = fD u := by
  set Lh : Set ℂ := {r : ℂ | 0 < s * r.im} with hLh
  have hLhO : IsOpen Lh := isOpen_sim_gt' s 0
  have hLhC : Convex ℝ Lh := convex_sim_gt' s 0
  -- S3
  have S3 : Set.EqOn fA Φ {r | 1 < s * r.im} := by
    obtain ⟨hz1, hz2⟩ := point_mem' s hs (-3) 2
    refine eqOn_of_convex_open (convex_sim_gt' s 1) (isOpen_sim_gt' s 1) (fun u hu => ?_)
      (fun u hu => hΦ u (by have : 1 < s*u.im := hu; linarith))
      ((isOpen_re_lt' (-2)).inter (isOpen_sim_gt' s 1)) Set.inter_subset_right
      (z₀ := (-3 : ℝ) + ((2 * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · have hu' : 1 < s * u.im := hu
      have h1u : 0 < s * (1+u).im := by
        simp only [Complex.add_im, Complex.one_im, zero_add]; linarith
      exact hA u (one_lt_norm_one_add_of_sim' hs hu') (mem_slitPlane_of_sim' h1u)
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hre, him⟩
      exact hAΦ r hre him
  -- S6
  have S6 : Set.EqOn fC Φ (Metric.ball (-1 : ℂ) 1 ∩ Lh) := by
    obtain ⟨hz1, hz2⟩ := point_mem' s hs (-3 / 4) (1 / 8)
    refine eqOn_of_convex_open ((convex_ball _ _).inter hLhC)
      (Metric.isOpen_ball.inter hLhO) (fun u hu => ?_) (fun u hu => hΦ u hu.2)
      (O := Metric.ball (-3 / 4 : ℂ) (1 / 4) ∩ Lh)
      (Metric.isOpen_ball.inter hLhO) ?_
      (z₀ := ((-3 / 4 : ℝ) : ℂ) + (((1 / 8) * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · have hb := hu.1
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm] at hb
      exact hC u hb hu.2
    · intro r ⟨hb, hl⟩
      refine ⟨?_, hl⟩
      rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
      calc ‖r - -1‖ = ‖(r - -3 / 4) + 1 / 4‖ := by congr 1; ring
        _ ≤ ‖r - -3 / 4‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
        _ < 1 := by rw [show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]; linarith
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((-3 / 4 : ℝ) : ℂ) + (((1 / 8) * s : ℝ) : ℂ) * Complex.I - -3 / 4 =
          (((1 / 8) * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rcases hs with rfl | rfl <;> norm_num
    · simp only [hLh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hb, hl⟩
      exact hCΦ r hb hl
  -- S7
  have S7 : Set.EqOn fD Φ ({r | -1 / 2 < r.re} ∩ Lh) := by
    obtain ⟨hz1, hz2⟩ := point_mem' s hs (-1 / 4) (1 / 4)
    refine eqOn_of_convex_open ((convex_re_gt' _).inter hLhC)
      ((isOpen_re_gt' _).inter hLhO) (fun u hu => ?_) (fun u hu => hΦ u hu.2)
      (O := (Metric.ball (-1 / 2 : ℂ) (1 / 2) ∩ {r : ℂ | -1 / 2 < r.re}) ∩ Lh)
      ((Metric.isOpen_ball.inter (isOpen_re_gt' _)).inter hLhO)
      (fun r hr' => ⟨hr'.1.2, hr'.2⟩)
      (z₀ := ((-1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I)
      ⟨⟨?_, ?_⟩, ?_⟩ ?_
    · have hre : -1 / 2 < u.re := hu.1
      have him : 0 < s * u.im := hu.2
      have h1u : 0 < s * (1+u).im := by
        simp only [Complex.add_im, Complex.one_im, zero_add]; exact him
      exact hD u (norm_lt_norm_one_add' hre) (mem_slitPlane_of_sim' him)
        (mem_slitPlane_of_sim' h1u)
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((-1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I - -1 / 2 =
          ((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this]
      have hn : ‖((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I‖ ^ 2 = 1 / 8 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
        have := sign_cases hs
        linear_combination (1 / 16) * this
      have h0 := norm_nonneg (((1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I)
      nlinarith
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · simp only [hLh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨⟨hb, hre⟩, hl⟩
      have hre : -1 / 2 < r.re := hre
      have hCm : r ∈ Metric.ball (-1 : ℂ) 1 ∩ Lh := by
        refine ⟨?_, hl⟩
        rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
        calc ‖r - -1‖ = ‖(r - -1 / 2) + 1 / 2‖ := by congr 1; ring
          _ ≤ ‖r - -1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
          _ < 1 := by rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; linarith
      rw [← hCD r hb hre hl]
      exact S6 hCm
  -- S8
  have S8 : Set.EqOn fA fD {r | 0 < r.re} := by
    obtain ⟨hz1, hz2⟩ := point_mem' s hs 1 2
    refine eqOn_of_convex_open (convex_re_gt' 0) (isOpen_re_gt' 0) (fun u hu => ?_)
      (fun u hu => ?_) ((isOpen_sim_gt' s 1).inter (isOpen_re_gt' 0)) Set.inter_subset_right
      (z₀ := ((1 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · have hre : 0 < u.re := hu
      have h1 : 1 < ‖1 + u‖ := lt_of_lt_of_le (by simp; linarith) (Complex.re_le_norm _)
      exact hA u h1 (Or.inl (by simp; linarith))
    · have hre : 0 < u.re := hu
      exact hD u (norm_lt_norm_one_add' (by linarith)) (Or.inl hre) (Or.inl (by simp; linarith))
    · simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · intro r ⟨him, hre⟩
      have him : 1 < s * r.im := him
      have hre : 0 < r.re := hre
      rw [S3 him, S7 ⟨(by linarith : -1 / 2 < r.re), (by linarith : 0 < s * r.im)⟩]
  intro u hu
  exact S8 hu

end VOA.Huang.LogBraided
