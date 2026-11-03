/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bLaurent
import VOA.Classification.COne.McRaeM2LogBraidedHalfPlane

/-! # O5b, gluing: one holomorphic function on `ℂ ∖ {0, 1}` from three single-valued channels

Pure complex analysis, used for the four-point function `ζ ↦ ⟨f, Y(u, ζ) Y(v, 1) x⟩` of a twisted
summand (`u` at `ζ`, `v` at `1`, `x` at `0`).

* `exists_rowEval_slit`: a shifted solution of a rational Fuchsian equation with its only
  finite pole at `x = 1` (the rows of products of logarithmic intertwining operators,
  `exists_ratFuchsian_log_product_homogeneous`) continues holomorphically to `ℂ ∖ [1, ∞)`. The
  library gives the two open half planes (`exists_rowEval_halfPlane`); the negative real axis is
  covered by the Möbius chart `x = -v/(1-v)` (`chart_continuation` with `q = 1`).
* `exists_glue`: given the product channel `A` continued to `ℂ ∖ [0,1]` (`Φ`), the reversed
  product channel `C` (on `0 < |ζ| < 1`), the iterate channel `D` (on `0 < |ζ-1| < 1`), with
  `A = D` on `(1, 3/2)` and `C = D` on `(1/2, 1)`, there is one function holomorphic on
  `ℂ ∖ {0, 1}` equal to the three channels on their domains.
* `residue_of_channels`: hence the three Laurent coefficient sequences satisfy the residue
  identity (`residue_of_glue`).

No `sorry`, no new axioms.
-/

noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open VOA Complex Filter Topology Set
open VOA.Huang.LogBraided (rowEval)
open VOA.Huang.Convergence (RatFuchsian)
open scoped BigOperators

/-! ## Identity-theorem helpers -/

theorem frequently_real {f g : ℂ → ℂ} {a b x₀ : ℝ} (ha : a < x₀) (hb : x₀ < b)
    (h : ∀ x : ℝ, a < x → x < b → f x = g x) : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), f z = g z := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.mp hU
  set d : ℝ := min ε (b - x₀) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; have := lt_min hε (sub_pos.mpr hb); positivity
  have hdε : d < ε := by rw [hd]; have := min_le_left ε (b - x₀); linarith
  have hdb : d < b - x₀ := by rw [hd]; have := min_le_right ε (b - x₀); linarith
  refine ⟨((x₀ + d : ℝ) : ℂ), hεU ⟨?_, ?_⟩, h _ (by linarith) (by linarith)⟩
  · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show x₀ + d - x₀ = d by ring, abs_of_pos hd0]
    exact hdε
  · intro h'
    have h'' : ((x₀ + d : ℝ) : ℂ) = (x₀ : ℂ) := h'
    have : x₀ + d = x₀ := by exact_mod_cast h''
    linarith

/-- Identity theorem on a convex set from agreement on an open subset. -/
theorem eqOn_convex {f g : ℂ → ℂ} {U O : Set ℂ} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hf : ∀ z ∈ U, DifferentiableAt ℂ f z) (hg : ∀ z ∈ U, DifferentiableAt ℂ g z)
    (hO : IsOpen O) (hOU : O ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ O) (hfg : Set.EqOn f g O) :
    Set.EqOn f g U :=
  VOA.Huang.TensorCat.HexagonClose.eqOn_of_convex' hUc
    (DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUo)
    (DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUo)
    hO hOU hz₀ hfg

/-- Identity theorem on a convex set from frequent agreement. -/
theorem eqOn_convex_freq {f g : ℂ → ℂ} {U : Set ℂ} (hUc : Convex ℝ U) (hUo : IsOpen U)
    (hf : ∀ z ∈ U, DifferentiableAt ℂ f z) (hg : ∀ z ∈ U, DifferentiableAt ℂ g z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : Set.EqOn f g U :=
  (DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUo)
    |>.eqOn_of_preconnected_of_frequently_eq
    (DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUo)
    hUc.isPreconnected hz₀ hfg

/-! ## Elementary open convex sets -/

theorem convex_ball_inter_re_gt (c : ℂ) (r x : ℝ) :
    Convex ℝ (Metric.ball c r ∩ {z : ℂ | x < z.re}) :=
  (convex_ball c r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.re)
    ⟨fun a b => by simp, fun a b => by simp⟩ x)

theorem convex_ball_inter_re_lt (c : ℂ) (r x : ℝ) :
    Convex ℝ (Metric.ball c r ∩ {z : ℂ | z.re < x}) :=
  (convex_ball c r).inter (convex_halfSpace_lt (f := fun z : ℂ => z.re)
    ⟨fun a b => by simp, fun a b => by simp⟩ x)

theorem convex_ball_inter_im_gt (c : ℂ) (r : ℝ) :
    Convex ℝ (Metric.ball c r ∩ {z : ℂ | 0 < z.im}) :=
  (convex_ball c r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im)
    ⟨fun a b => by simp, fun a b => by simp⟩ 0)

theorem convex_ball_inter_im_lt (c : ℂ) (r : ℝ) :
    Convex ℝ (Metric.ball c r ∩ {z : ℂ | z.im < 0}) :=
  (convex_ball c r).inter (convex_halfSpace_lt (f := fun z : ℂ => z.im)
    ⟨fun a b => by simp, fun a b => by simp⟩ 0)

theorem isOpen_re_gt' (x : ℝ) : IsOpen {z : ℂ | x < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isOpen_re_lt' (x : ℝ) : IsOpen {z : ℂ | z.re < x} :=
  isOpen_lt Complex.continuous_re continuous_const

theorem isOpen_im_gt' : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem isOpen_im_lt' : IsOpen {z : ℂ | z.im < 0} :=
  isOpen_lt Complex.continuous_im continuous_const

/-- The segment `[0, 1]`. -/
def seg01 : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1}

theorem isClosed_seg01 : IsClosed seg01 :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))

theorem mem_ball_one_iff (z : ℂ) : z ∈ Metric.ball (1 : ℂ) 1 ↔ ‖z - 1‖ < 1 := by
  rw [Metric.mem_ball, dist_eq_norm]

theorem mem_ball_zero_iff' (z : ℂ) : z ∈ Metric.ball (0 : ℂ) 1 ↔ ‖z‖ < 1 := by
  rw [Metric.mem_ball, dist_zero_right]

theorem norm_eq_of_im_zero {z : ℂ} (h : z.im = 0) : ‖z‖ = |z.re| := by
  rw [← Complex.re_add_im z, h]; simp

theorem norm_sub_one_of_im_zero {z : ℂ} (h : z.im = 0) : ‖z - 1‖ = |z.re - 1| := by
  have : (z - 1).im = 0 := by simp [h]
  rw [norm_eq_of_im_zero this]; simp

/-! ## Points -/

theorem norm_mk_le (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ |x| + |y| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

theorem re_mk (x y : ℝ) : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp

theorem im_mk (x y : ℝ) : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp

theorem sub_one_mk (x y : ℝ) :
    (x : ℂ) + (y : ℂ) * Complex.I - 1 = ((x - 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
  push_cast; ring

theorem mk_ne_zero {x y : ℝ} (h : y ≠ 0) : (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
  intro h0; apply h; have := congrArg Complex.im h0; simpa using this

theorem mk_ne_one {x y : ℝ} (h : y ≠ 0) : (x : ℂ) + (y : ℂ) * Complex.I ≠ 1 := by
  intro h0; apply h; have := congrArg Complex.im h0; simpa using this

theorem mk_not_seg {x y : ℝ} (h : y ≠ 0) : (x : ℂ) + (y : ℂ) * Complex.I ∉ seg01 := by
  rintro ⟨h0, -, -⟩; rw [im_mk] at h0; exact h h0

/-! ## The gluing theorem -/

section Glue
variable {fC fD Φ : ℂ → ℂ}

/-- **Gluing three channels.** -/
theorem exists_glue
    (hΦd : ∀ ζ : ℂ, ζ ∉ seg01 → DifferentiableAt ℂ Φ ζ)
    (hCd : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → DifferentiableAt ℂ fC ζ)
    (hDd : ∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < 1 → DifferentiableAt ℂ fD ζ)
    (hAD : ∀ x : ℝ, 1 < x → x < 3 / 2 → Φ x = fD x)
    (hCD : ∀ x : ℝ, 1 / 2 < x → x < 1 → fC x = fD x) :
    ∃ Ψ : ℂ → ℂ, (∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → DifferentiableAt ℂ Ψ ζ) ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → Ψ ζ = Φ ζ) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → Ψ ζ = fC ζ) ∧
      (∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < 1 → Ψ ζ = fD ζ) := by
  classical
  -- (1) `Φ = fD` on the disc around `1` minus the segment
  have hR : Set.EqOn Φ fD (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 1 < z.re}) := by
    refine eqOn_convex_freq (convex_ball_inter_re_gt 1 1 1)
      (Metric.isOpen_ball.inter (isOpen_re_gt' 1)) (fun z hz => hΦd z ?_)
      (fun z hz => hDd z ?_ ((mem_ball_one_iff z).mp hz.1)) (z₀ := ((5 / 4 : ℝ) : ℂ)) ⟨?_, ?_⟩
      (frequently_real (a := 1) (b := 3 / 2) (by norm_num) (by norm_num) hAD)
    · rintro ⟨-, -, h⟩; have : 1 < z.re := hz.2; linarith
    · rintro rfl; have : (1 : ℝ) < (1 : ℂ).re := hz.2; simp at this
    · rw [mem_ball_one_iff, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
      norm_num
    · show (1 : ℝ) < ((5 / 4 : ℝ) : ℂ).re; simp; norm_num
  have hUp : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Set.EqOn Φ fD (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) := by
    intro s hs
    have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hconv : Convex ℝ (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) :=
      (convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => s * z.im)
        ⟨fun a b => by simp; ring, fun a b => by simp; ring⟩ 0)
    have hopen : IsOpen (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (continuous_const.mul Complex.continuous_im))
    have hz₀ : ((3 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I ∈
        (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) ∩
          (Metric.ball (1 : ℂ) 1 ∩ {z : ℂ | 1 < z.re}) := by
      have hb : ((3 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (1 : ℂ) 1 := by
        rw [mem_ball_one_iff, sub_one_mk]
        refine lt_of_le_of_lt (norm_mk_le _ _) ?_
        rw [show |s / 4| = 1 / 4 by rw [abs_div, habs]; norm_num]; norm_num
      refine ⟨⟨hb, ?_⟩, hb, ?_⟩
      · show 0 < s * ((((3 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)).im
        rw [im_mk]; nlinarith
      · show (1 : ℝ) < ((((3 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)).re
        rw [re_mk]; norm_num
    refine eqOn_convex hconv hopen (fun z hz => hΦd z ?_) (fun z hz => hDd z ?_
      ((mem_ball_one_iff z).mp hz.1))
      (hopen.inter (Metric.isOpen_ball.inter (isOpen_re_gt' 1))) Set.inter_subset_left
      hz₀ (fun z hz => hR hz.2)
    · rintro ⟨h, -, -⟩; have := hz.2; simp only [Set.mem_setOf_eq, h, mul_zero] at this
      exact lt_irrefl _ this
    · rintro rfl; have := hz.2; simp at this
  have hDsl : ∀ z : ℂ, ‖z - 1‖ < 1 → z ∉ seg01 → Φ z = fD z := by
    intro z hz hzs
    have hb : z ∈ Metric.ball (1 : ℂ) 1 := (mem_ball_one_iff z).mpr hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact hUp (-1) (Or.inr rfl) ⟨hb, by show 0 < -1 * z.im; linarith⟩
    · refine hR ⟨hb, ?_⟩
      show 1 < z.re
      by_contra hc
      push Not at hc
      apply hzs
      refine ⟨h, ?_, hc⟩
      rw [norm_sub_one_of_im_zero h] at hz
      have := abs_lt.mp hz; linarith
    · exact hUp 1 (Or.inl rfl) ⟨hb, by show 0 < 1 * z.im; linarith⟩
  -- (2) `fC = fD` on the lens
  have hL : Set.EqOn fC fD (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1) := by
    refine eqOn_convex_freq ((convex_ball _ _).inter (convex_ball _ _))
      (Metric.isOpen_ball.inter Metric.isOpen_ball) (fun z hz => hCd z ?_ ?_)
      (fun z hz => hDd z ?_ ((mem_ball_one_iff z).mp hz.2)) (z₀ := ((3 / 4 : ℝ) : ℂ)) ⟨?_, ?_⟩
      (frequently_real (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) hCD)
    · rintro rfl; have := hz.2; rw [mem_ball_one_iff] at this; simp at this
    · exact (mem_ball_zero_iff' z).mp hz.1
    · rintro rfl; have := hz.1; rw [mem_ball_zero_iff'] at this; simp at this
    · rw [mem_ball_zero_iff', Complex.norm_real]; norm_num
    · rw [mem_ball_one_iff, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
      norm_num
  -- (3) `Φ = fC` on the punctured unit disc minus the segment
  have hVs : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Set.EqOn Φ fC (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) := by
    intro s hs
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hconv : Convex ℝ (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) :=
      (convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => s * z.im)
        ⟨fun a b => by simp; ring, fun a b => by simp; ring⟩ 0)
    have hopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (continuous_const.mul Complex.continuous_im))
    set O := (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}) ∩ Metric.ball (1 : ℂ) 1 with hO
    have hz₀ : ((1 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I ∈ O := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_ball_zero_iff']
        refine lt_of_le_of_lt (norm_mk_le _ _) ?_
        rw [show |s / 4| = 1 / 4 by rw [abs_div, habs]; norm_num]; norm_num
      · show 0 < s * ((((1 / 2 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)).im
        rw [im_mk]; rcases hs with rfl | rfl <;> norm_num
      · rw [mem_ball_one_iff, sub_one_mk]
        refine lt_of_le_of_lt (norm_mk_le _ _) ?_
        rw [show |s / 4| = 1 / 4 by rw [abs_div, habs]; norm_num]; norm_num
    have hnz : ∀ z ∈ Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < s * z.im}, z.im ≠ 0 := by
      intro z hz h0; have := hz.2; simp only [Set.mem_setOf_eq, h0, mul_zero] at this
      exact lt_irrefl _ this
    refine eqOn_convex hconv hopen (fun z hz => hΦd z ?_) (fun z hz => hCd z ?_
      ((mem_ball_zero_iff' z).mp hz.1)) (hopen.inter Metric.isOpen_ball) Set.inter_subset_left
      hz₀ ?_
    · rintro ⟨h, -, -⟩; exact hnz z hz h
    · rintro rfl; exact hnz 0 hz (by simp)
    · intro z hz
      have hzs : z ∉ seg01 := fun h => hnz z hz.1 h.1
      rw [hDsl z ((mem_ball_one_iff z).mp hz.2) hzs]
      exact (hL ⟨hz.1.1, hz.2⟩).symm
  have hVL : Set.EqOn Φ fC (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0}) := by
    have hconv := convex_ball_inter_re_lt (0 : ℂ) 1 0
    have hopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0}) :=
      Metric.isOpen_ball.inter (isOpen_re_lt' 0)
    have hz₀ : ((-1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I ∈
        (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0}) ∩
          (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < 1 * z.im}) := by
      have hb : ((-1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff']
        refine lt_of_le_of_lt (norm_mk_le _ _) ?_
        norm_num [abs_of_neg, abs_of_pos]
      refine ⟨⟨hb, ?_⟩, hb, ?_⟩
      · show ((((-1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I)).re < 0
        rw [re_mk]; norm_num
      · show 0 < 1 * ((((-1 / 4 : ℝ) : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I)).im
        rw [im_mk]; norm_num
    refine eqOn_convex hconv hopen (fun z hz => hΦd z ?_) (fun z hz => hCd z ?_
      ((mem_ball_zero_iff' z).mp hz.1))
      (hopen.inter (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (continuous_const.mul Complex.continuous_im)))) Set.inter_subset_left hz₀
      (fun z hz => hVs 1 (Or.inl rfl) hz.2)
    · rintro ⟨-, h, -⟩; have : z.re < 0 := hz.2; linarith
    · rintro rfl; have : (0 : ℂ).re < 0 := hz.2; simp at this
  have hCsl : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → z ∉ seg01 → Φ z = fC z := by
    intro z hz0 hz hzs
    have hb : z ∈ Metric.ball (0 : ℂ) 1 := (mem_ball_zero_iff' z).mpr hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact hVs (-1) (Or.inr rfl) ⟨hb, by show 0 < -1 * z.im; linarith⟩
    · refine hVL ⟨hb, ?_⟩
      show z.re < 0
      by_contra hc
      push Not at hc
      apply hzs
      refine ⟨h, hc, ?_⟩
      rw [norm_eq_of_im_zero h] at hz
      have := abs_lt.mp hz; linarith
    · exact hVs 1 (Or.inl rfl) ⟨hb, by show 0 < 1 * z.im; linarith⟩
  -- the glued function
  set Ψ : ℂ → ℂ := fun z => if ‖z - 1‖ < 1 then fD z else if ‖z‖ < 1 then fC z else Φ z
    with hΨ
  have hseg : ∀ z ∈ seg01, z ≠ 0 → ‖z - 1‖ < 1 := by
    rintro z ⟨h0, h1, h2⟩ hz0
    rw [norm_sub_one_of_im_zero h0, abs_lt]
    have : z.re ≠ 0 := by
      intro hre; apply hz0; rw [← Complex.re_add_im z, hre, h0]; simp
    have hpos : 0 < z.re := lt_of_le_of_ne h1 (Ne.symm this)
    constructor <;> linarith
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro ζ h0 h1
    by_cases hD : ‖ζ - 1‖ < 1
    · have hev : Ψ =ᶠ[𝓝 ζ] fD := by
        filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
          continuous_const).mem_nhds hD] with z hz
        simp only [hΨ, if_pos (show ‖z - 1‖ < 1 from hz)]
      exact (hDd ζ h1 hD).congr_of_eventuallyEq hev
    · by_cases hC : ‖ζ‖ < 1
      · have hev : Ψ =ᶠ[𝓝 ζ] fC := by
          filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hC,
            isOpen_compl_singleton.mem_nhds h0] with z hz hz0
          simp only [hΨ]
          split_ifs with h
          · exact (hL ⟨(mem_ball_zero_iff' z).mpr hz, (mem_ball_one_iff z).mpr h⟩).symm
          · rfl
        exact (hCd ζ h0 hC).congr_of_eventuallyEq hev
      · have hζs : ζ ∉ seg01 := by
          intro hs
          exact hD (hseg ζ hs h0)
        have hev : Ψ =ᶠ[𝓝 ζ] Φ := by
          filter_upwards [isClosed_seg01.isOpen_compl.mem_nhds hζs] with z hz
          simp only [hΨ]
          split_ifs with ha hb
          · exact (hDsl z ha hz).symm
          · have hz0 : z ≠ 0 := by
              rintro rfl; exact hz ⟨by simp, by simp, by simp⟩
            exact (hCsl z hz0 hb hz).symm
          · rfl
        exact (hΦd ζ hζs).congr_of_eventuallyEq hev
  · intro ζ hζ
    simp only [hΨ]
    split_ifs with ha hb
    · have hζs : ζ ∉ seg01 := by
        rintro ⟨h0, h1, h2⟩
        rw [norm_eq_of_im_zero h0, abs_of_nonneg h1] at hζ
        linarith
      exact (hDsl ζ ha hζs).symm
    · exact absurd hb (by linarith)
    · rfl
  · intro ζ h0 hζ
    simp only [hΨ]
    split_ifs with ha
    · exact (hL ⟨(mem_ball_zero_iff' ζ).mpr hζ, (mem_ball_one_iff ζ).mpr ha⟩).symm
    · rfl
  · intro ζ h1 hζ
    simp only [hΨ, if_pos hζ]

end Glue

/-! ## Continuation of a Fuchsian row to `ℂ ∖ [1, ∞)` -/

section Row
open VOA.Huang.TensorCat.HexagonClose (Lhs chart_continuation chartX chartM)
open VOA.Huang.FrobeniusLog (psEval halfPlane)

variable {c : ℕ → ℂ} {K : ℕ} {ν : ℂ} {Q : PowerSeries ℂ}

theorem summable_row (hQ : RatFuchsian 1 ν Q) (hc : ∀ n : ℕ, PowerSeries.coeff (n + K) Q = c n)
    {x : ℂ} (hx : ‖x‖ < 1) : Summable fun n => c n * x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx0
  · refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
    rw [Finset.mem_singleton] at hk
    rw [zero_pow hk, mul_zero]
  have hs := (VOA.Huang.Convergence.summable_of_ratFuchsian (by norm_num) hQ hx).of_norm
  have h2 := ((summable_nat_add_iff K).mpr hs).mul_left (x ^ K)⁻¹
  refine h2.congr fun n => ?_
  rw [← hc n, pow_add]
  field_simp

theorem differentiableAt_rowEval (hQ : RatFuchsian 1 ν Q)
    (hc : ∀ n : ℕ, PowerSeries.coeff (n + K) Q = c n) {x : ℂ} (hx : ‖x‖ < 1) :
    DifferentiableAt ℂ (rowEval c) x :=
  VOA.Huang.HKLLoc.differentiableAt_powerSeries c (fun _ hq => summable_row hQ hc hq) hx

/-- `psEval` minus its first `K` terms, divided by `x^K`, is the shifted row. -/
theorem rowEval_eq_psEval (hQ : RatFuchsian 1 ν Q)
    (hc : ∀ n : ℕ, PowerSeries.coeff (n + K) Q = c n) {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    (psEval Q x - ∑ n ∈ Finset.range K, PowerSeries.coeff n Q * x ^ n) / x ^ K =
      rowEval c x := by
  have hsum := (VOA.Huang.Convergence.summable_of_ratFuchsian (by norm_num) hQ hx).of_norm
  rw [psEval, ← hsum.sum_add_tsum_nat_add K, add_sub_cancel_left, rowEval]
  have he : ∑' n : ℕ, PowerSeries.coeff (n + K) Q * x ^ (n + K) =
      x ^ K * ∑' n : ℕ, c n * x ^ n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hc, pow_add]; ring
  rw [he, mul_div_cancel_left₀ _ (pow_ne_zero K hx0)]

theorem norm_lt_norm_sub_one {x : ℂ} (hx : x.re < 0) : ‖x‖ < ‖x - 1‖ := by
  have h1 : ‖x‖ ^ 2 < ‖x - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem one_le_norm_sub_one {x : ℂ} (hx : x.re < 0) : 1 ≤ ‖x - 1‖ := by
  have := Complex.abs_re_le_norm (x - 1)
  rw [Complex.sub_re, Complex.one_re] at this
  rw [abs_of_neg (by linarith)] at this
  linarith

theorem re_div_sub_one_pos {x : ℂ} (hx : x.re < 0) : 0 < (x / (x - 1)).re := by
  have hx1 : x - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Complex.div_re]
  have hn : 0 < Complex.normSq (x - 1) := Complex.normSq_pos.mpr hx1
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [← add_div]
  apply div_pos _ hn
  nlinarith [sq_nonneg x.im]

/-- **A Fuchsian row continues to `ℂ ∖ [1, ∞)`.** -/
theorem exists_rowEval_slit (hQ : RatFuchsian 1 ν Q)
    (hc : ∀ n : ℕ, PowerSeries.coeff (n + K) Q = c n) :
    ∃ Ψ : ℂ → ℂ, (∀ x : ℂ, ¬(x.im = 0 ∧ 1 ≤ x.re) → DifferentiableAt ℂ Ψ x) ∧
      ∀ x : ℂ, ‖x‖ < 1 → Ψ x = rowEval c x := by
  classical
  obtain ⟨Ψp, hPa, hPe⟩ := VOA.Huang.LogBraided.exists_rowEval_halfPlane hQ hc
    (s := 1) (by norm_num)
  obtain ⟨Ψm, hMa, hMe⟩ := VOA.Huang.LogBraided.exists_rowEval_halfPlane hQ hc
    (s := -1) (by norm_num)
  have hQ' := hQ
  obtain ⟨s₀, bb, cc, p, hcp, hG⟩ := hQ'
  have hcp' : ∀ i < s₀, (1 - PowerSeries.X) ^ bb * cc i = (p i : PowerSeries ℂ) := by
    intro i hi
    have h := hcp i hi
    rwa [map_one, one_mul] at h
  obtain ⟨Gh, hGd, hGe⟩ := chart_continuation hcp' hG (q := 1) one_ne_zero (by simp)
  set ΨL : ℂ → ℂ := fun x => (Gh (Complex.log (x / (x - 1))) -
    ∑ n ∈ Finset.range K, PowerSeries.coeff n Q * x ^ n) / x ^ K with hΨL
  have hx0 : ∀ x : ℂ, x.re < 0 → x ≠ 0 := by
    rintro x hx rfl; simp at hx
  have hx1 : ∀ x : ℂ, x.re < 0 → x - 1 ≠ 0 := by
    intro x hx h; have := congrArg Complex.re h; simp at this; linarith
  have hslit : ∀ x : ℂ, x.re < 0 → x / (x - 1) ∈ Complex.slitPlane := fun x hx =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (re_div_sub_one_pos hx))
  have hvnorm : ∀ x : ℂ, x.re < 0 → ‖x / (x - 1)‖ < 1 := by
    intro x hx
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hx1 x hx))]
    exact norm_lt_norm_sub_one hx
  have hlogre : ∀ x : ℂ, x.re < 0 → (Complex.log (x / (x - 1))).re < 0 := by
    intro x hx
    rw [Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr (div_ne_zero (hx0 x hx) (hx1 x hx))) (hvnorm x hx)
  have hLd : ∀ x : ℂ, x.re < 0 → DifferentiableAt ℂ ΨL x := by
    intro x hx
    have hd1 : DifferentiableAt ℂ (fun y : ℂ => y / (y - 1)) x :=
      differentiableAt_id.div (differentiableAt_id.sub_const 1) (hx1 x hx)
    have hGx : DifferentiableAt ℂ Gh (Complex.log (x / (x - 1))) :=
      (hGd _ (hlogre x hx)).differentiableAt
        (VOA.Huang.FrobeniusLog.isOpen_halfPlane.mem_nhds (hlogre x hx))
    refine DifferentiableAt.div (DifferentiableAt.sub (hGx.comp x (hd1.clog (hslit x hx))) ?_)
      (differentiableAt_id.pow K) (pow_ne_zero K (hx0 x hx))
    exact DifferentiableAt.fun_sum fun n _ => (differentiableAt_const _).mul
      (differentiableAt_id.pow n)
  -- `ΨL` is the row near `0`
  have hLsmall : ∀ x : ℂ, x.re < 0 → ‖x‖ < 1 / 4 → ΨL x = rowEval c x := by
    intro x hx hxs
    have hv0 : x / (x - 1) ≠ 0 := div_ne_zero (hx0 x hx) (hx1 x hx)
    have hτ : (Complex.log (x / (x - 1))).re < -chartM 1 := by
      rw [Complex.log_re, chartM, norm_one, show (2 : ℝ) + 2 * 1 = 4 by norm_num,
        ← Real.log_inv]
      refine Real.log_lt_log (norm_pos_iff.mpr hv0) ?_
      rw [norm_div]
      have h1 := one_le_norm_sub_one hx
      calc ‖x‖ / ‖x - 1‖ ≤ ‖x‖ := div_le_self (norm_nonneg _) h1
        _ < 1 / 4 := hxs
        _ = 4⁻¹ := by norm_num
    have hGx := hGe _ hτ
    rw [Complex.exp_log hv0] at hGx
    have hchart : chartX 1 (x / (x - 1)) = x := by
      rw [chartX]
      have := hx1 x hx
      field_simp
      ring
    rw [hchart] at hGx
    simp only [hΨL]
    rw [hGx]
    exact rowEval_eq_psEval hQ hc (hx0 x hx) (by linarith)
  have hLrow : Set.EqOn ΨL (rowEval c) (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | z.re < 0}) := by
    refine eqOn_convex (convex_ball_inter_re_lt 0 1 0) (Metric.isOpen_ball.inter (isOpen_re_lt' 0))
      (fun z hz => hLd z hz.2) (fun z hz => differentiableAt_rowEval hQ hc
        ((mem_ball_zero_iff' z).mp hz.1))
      (Metric.isOpen_ball.inter (isOpen_re_lt' 0)) (O := Metric.ball (0 : ℂ) (1 / 4) ∩
        {z : ℂ | z.re < 0}) (fun z hz => ⟨Metric.ball_subset_ball (by norm_num) hz.1, hz.2⟩)
      (z₀ := ((-1 / 8 : ℝ) : ℂ)) ⟨?_, ?_⟩ ?_
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real]; norm_num
    · show ((-1 / 8 : ℝ) : ℂ).re < 0; simp; norm_num
    · intro z hz
      exact hLsmall z hz.2 (by rw [← dist_zero_right]; exact hz.1)
  have hLhalf : ∀ (s : ℝ) (Ψs : ℂ → ℂ), (s = 1 ∨ s = -1) → AnalyticOnNhd ℂ Ψs (Lhs s) →
      (∀ w ∈ Lhs s, ‖w‖ < 1 → Ψs w = rowEval c w) →
      Set.EqOn ΨL Ψs ({z : ℂ | z.re < 0} ∩ {z : ℂ | 0 < s * z.im}) := by
    intro s Ψs hs hA hE
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hconv : Convex ℝ ({z : ℂ | z.re < 0} ∩ {z : ℂ | 0 < s * z.im}) :=
      (convex_halfSpace_lt (f := fun z : ℂ => z.re) ⟨fun a b => by simp, fun a b => by simp⟩
        0).inter (convex_halfSpace_gt (f := fun z : ℂ => s * z.im)
        ⟨fun a b => by simp; ring, fun a b => by simp; ring⟩ 0)
    have hopen : IsOpen ({z : ℂ | z.re < 0} ∩ {z : ℂ | 0 < s * z.im}) :=
      (isOpen_re_lt' 0).inter (isOpen_lt continuous_const
        (continuous_const.mul Complex.continuous_im))
    refine eqOn_convex hconv hopen (fun z hz => hLd z hz.1)
      (fun z hz => (hA z hz.2).differentiableAt) (hopen.inter Metric.isOpen_ball)
      (O := ({z : ℂ | z.re < 0} ∩ {z : ℂ | 0 < s * z.im}) ∩ Metric.ball (0 : ℂ) 1)
      Set.inter_subset_left (z₀ := ((-1 / 4 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)
      ⟨⟨?_, ?_⟩, ?_⟩ ?_
    · show ((((-1 / 4 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)).re < 0
      rw [re_mk]; norm_num
    · show 0 < s * ((((-1 / 4 : ℝ) : ℂ) + ((s / 4 : ℝ) : ℂ) * Complex.I)).im
      rw [im_mk]; rcases hs with rfl | rfl <;> norm_num
    · rw [mem_ball_zero_iff']
      refine lt_of_le_of_lt (norm_mk_le _ _) ?_
      rw [show |s / 4| = 1 / 4 by rw [abs_div, habs]; norm_num]; norm_num [abs_of_neg]
    · intro z hz
      rw [hLrow ⟨hz.2, hz.1.1⟩, hE z hz.1.2 ((mem_ball_zero_iff' z).mp hz.2)]
  have hLp := hLhalf 1 Ψp (Or.inl rfl) hPa hPe
  have hLm := hLhalf (-1) Ψm (Or.inr rfl) hMa hMe
  set Ψ : ℂ → ℂ := fun x => if ‖x‖ < 1 then rowEval c x else if 0 < x.im then Ψp x
    else if x.im < 0 then Ψm x else ΨL x with hΨ
  refine ⟨Ψ, fun x hx => ?_, fun x hx => by simp only [hΨ, if_pos hx]⟩
  by_cases h1 : ‖x‖ < 1
  · have hev : Ψ =ᶠ[𝓝 x] rowEval c := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h1] with z hz
      simp only [hΨ, if_pos (show ‖z‖ < 1 from hz)]
    exact (differentiableAt_rowEval hQ hc h1).congr_of_eventuallyEq hev
  rcases lt_trichotomy x.im 0 with him | him | him
  · have hev : Ψ =ᶠ[𝓝 x] Ψm := by
      filter_upwards [isOpen_im_lt'.mem_nhds him] with z hz
      have hz' : z.im < 0 := hz
      simp only [hΨ]
      split_ifs with ha hb
      · exact (hMe z (by show 0 < -1 * z.im; linarith) ha).symm
      · linarith
      · rfl
    exact ((hMa x (by show 0 < -1 * x.im; linarith)).differentiableAt).congr_of_eventuallyEq hev
  · have hre : x.re < 0 := by
      have hn := norm_eq_of_im_zero him
      push Not at h1
      have : x.re < 1 := by
        by_contra hc; exact hx ⟨him, by linarith⟩
      rw [hn] at h1
      rcases le_or_gt 0 x.re with h | h
      · rw [abs_of_nonneg h] at h1; linarith
      · exact h
    have hev : Ψ =ᶠ[𝓝 x] ΨL := by
      filter_upwards [(isOpen_re_lt' 0).mem_nhds hre] with z hz
      have hz' : z.re < 0 := hz
      simp only [hΨ]
      split_ifs with ha hb hc
      · exact (hLrow ⟨(mem_ball_zero_iff' z).mpr ha, hz'⟩).symm
      · exact (hLp ⟨hz', by show 0 < 1 * z.im; linarith⟩).symm
      · exact (hLm ⟨hz', by show 0 < -1 * z.im; linarith⟩).symm
      · rfl
    exact (hLd x hre).congr_of_eventuallyEq hev
  · have hev : Ψ =ᶠ[𝓝 x] Ψp := by
      filter_upwards [isOpen_im_gt'.mem_nhds him] with z hz
      have hz' : 0 < z.im := hz
      simp only [hΨ]
      split_ifs with ha
      · exact (hPe z (by show 0 < 1 * z.im; linarith) ha).symm
      · rfl
    exact ((hPa x (by show 0 < 1 * x.im; linarith)).differentiableAt).congr_of_eventuallyEq hev

end Row

/-! ## Channels given by Laurent series -/

theorem hasSum_of_nat_shift {u : ℤ → ℂ} {n₁ : ℤ} (hu : ∀ n, n < n₁ → u n = 0) {ζ : ℂ}
    (hζ0 : ζ ≠ 0) {X : ℂ} (h : HasSum (fun k : ℕ => u (k + n₁) * ζ ^ k) X) :
    HasSum (fun n : ℤ => u n * ζ ^ n) (ζ ^ n₁ * X) := by
  have h2 := h.mul_left (ζ ^ n₁)
  let g : ℕ → ℤ := fun k => k + n₁
  have hg : Function.Injective g := fun i j hij => by simpa [g] using hij
  have hf : ∀ n ∉ Set.range g, u n * ζ ^ n = 0 := by
    intro n hn
    have : n < n₁ := by
      by_contra hc; exact hn ⟨(n - n₁).toNat, by simp only [g]; omega⟩
    rw [hu n this, zero_mul]
  refine (hg.hasSum_iff hf).mp (h2.congr_fun fun k => ?_)
  simp only [Function.comp_apply, g]
  rw [zpow_add₀ hζ0, zpow_natCast]; ring

theorem summable_nat_shift {u : ℤ → ℂ} {n₁ : ℤ} {ζ : ℂ} (hζ0 : ζ ≠ 0)
    (h : Summable fun n : ℤ => u n * ζ ^ n) : Summable fun k : ℕ => u (k + n₁) * ζ ^ k := by
  have h1 := (h.comp_injective (i := fun k : ℕ => (k : ℤ) + n₁)
    (fun i j hij => by simpa using hij)).mul_left (ζ ^ n₁)⁻¹
  refine h1.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [zpow_add₀ hζ0, zpow_natCast]; field_simp

/-- A Laurent series with finitely many negative powers, summable on the punctured unit disc, is
holomorphic there. -/
theorem differentiableAt_laurent {u : ℤ → ℂ} {n₁ : ℤ} (hu : ∀ n, n < n₁ → u n = 0)
    (hsum : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → Summable fun n : ℤ => u n * ζ ^ n) {ζ : ℂ}
    (hζ0 : ζ ≠ 0) (hζ1 : ‖ζ‖ < 1) :
    DifferentiableAt ℂ (fun z => ∑' n : ℤ, u n * z ^ n) ζ := by
  have hps : ∀ q : ℂ, ‖q‖ < 1 → Summable fun k : ℕ => u (k + n₁) * q ^ k := by
    intro q hq
    rcases eq_or_ne q 0 with rfl | hq0
    · refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
      rw [Finset.mem_singleton] at hk
      rw [zero_pow hk, mul_zero]
    · exact summable_nat_shift hq0 (hsum q hq0 hq)
  have hg := VOA.Huang.HKLLoc.differentiableAt_powerSeries _ hps hζ1
  have hev : (fun z => ∑' n : ℤ, u n * z ^ n) =ᶠ[𝓝 ζ]
      fun z => z ^ n₁ * ∑' k : ℕ, u (k + n₁) * z ^ k := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hζ0,
      (isOpen_lt continuous_norm continuous_const).mem_nhds hζ1] with z hz0 hz1
    exact (hasSum_of_nat_shift hu hz0 (hps z hz1).hasSum).tsum_eq
  exact ((differentiableAt_id.zpow (Or.inl hζ0)).mul hg).congr_of_eventuallyEq hev

theorem inv_not_mem_ray {ζ : ℂ} (hζ : ζ ∉ seg01) : ¬((ζ⁻¹).im = 0 ∧ 1 ≤ (ζ⁻¹).re) := by
  rintro ⟨him, hre⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hre; linarith
  apply hζ
  have hw : ζ⁻¹ = ((ζ⁻¹).re : ℂ) := by
    rw [← Complex.re_add_im ζ⁻¹, him]; simp
  have hz : ζ = (((ζ⁻¹).re)⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv, ← hw, inv_inv]
  rw [hz]
  refine ⟨by simp, by simp only [Complex.ofReal_re]; positivity, ?_⟩
  simp only [Complex.ofReal_re]
  exact inv_le_one_of_one_le₀ hre

/-- **The residue identity from three single-valued channels.** -/
theorem residue_of_channels {s t q : ℤ → ℂ} {n₀ n₁ m₁ : ℤ}
    (hs0 : ∀ n, n₀ < n → s n = 0) (ht0 : ∀ n, n < n₁ → t n = 0) (hq0 : ∀ m, m < m₁ → q m = 0)
    (hrow : ∃ (K : ℕ) (ν : ℂ) (Q : PowerSeries ℂ), RatFuchsian 1 ν Q ∧
      ∀ k : ℕ, PowerSeries.coeff (k + K) Q = s (n₀ - k))
    (hT : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → Summable fun n : ℤ => t n * ζ ^ n)
    (hQ : ∀ r : ℂ, r ≠ 0 → ‖r‖ < 1 → Summable fun m : ℤ => q m * r ^ m)
    (hAD : ∀ x : ℝ, 1 < x → x < 3 / 2 →
      ∑' n : ℤ, s n * (x : ℂ) ^ n = ∑' m : ℤ, q m * ((x : ℂ) - 1) ^ m)
    (hCD : ∀ x : ℝ, 1 / 2 < x → x < 1 →
      ∑' n : ℤ, t n * (x : ℂ) ^ n = ∑' m : ℤ, q m * ((x : ℂ) - 1) ^ m)
    (a ℓ : ℤ) : resInf a ℓ s - resZero a ℓ t = resOne a ℓ q := by
  classical
  obtain ⟨K, ν, Q, hQF, hc⟩ := hrow
  obtain ⟨Ψr, hΨrd, hΨre⟩ := exists_rowEval_slit hQF (c := fun k => s (n₀ - k)) hc
  -- the product channel and its continuation
  have hA : ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℤ => s n * ζ ^ n) (ζ ^ n₀ * Ψr ζ⁻¹) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ; linarith
    have hw : ‖ζ⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hζ
    rw [hΨre _ hw]
    have h1 := (summable_row hQF hc hw).hasSum.mul_left (ζ ^ n₀)
    let g : ℕ → ℤ := fun k => n₀ - k
    have hg : Function.Injective g := fun i j hij => by simpa [g] using hij
    have hf : ∀ n ∉ Set.range g, s n * ζ ^ n = 0 := by
      intro n hn
      have : n₀ < n := by
        by_contra hc'; exact hn ⟨(n₀ - n).toNat, by simp only [g]; omega⟩
      rw [hs0 n this, zero_mul]
    refine (hg.hasSum_iff hf).mp (h1.congr_fun fun k => ?_)
    simp only [Function.comp_apply, g]
    rw [zpow_sub₀ hζ0, zpow_natCast, inv_pow]; field_simp
  set Φ : ℂ → ℂ := fun ζ => ζ ^ n₀ * Ψr ζ⁻¹ with hΦ
  have hΦd : ∀ ζ : ℂ, ζ ∉ seg01 → DifferentiableAt ℂ Φ ζ := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; exact hζ ⟨by simp, by simp, by simp⟩
    exact (differentiableAt_id.zpow (Or.inl hζ0)).mul
      ((hΨrd _ (inv_not_mem_ray hζ)).comp ζ (differentiableAt_inv hζ0))
  set fC : ℂ → ℂ := fun ζ => ∑' n : ℤ, t n * ζ ^ n with hfC
  set fD : ℂ → ℂ := fun ζ => ∑' m : ℤ, q m * (ζ - 1) ^ m with hfD
  have hCd : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → DifferentiableAt ℂ fC ζ :=
    fun ζ h0 h1 => differentiableAt_laurent ht0 hT h0 h1
  have hDd : ∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < 1 → DifferentiableAt ℂ fD ζ := by
    intro ζ h0 h1
    have := differentiableAt_laurent hq0 hQ (sub_ne_zero.mpr h0) h1
    exact this.comp ζ (differentiableAt_id.sub_const 1)
  have hAD' : ∀ x : ℝ, 1 < x → x < 3 / 2 → Φ x = fD x := by
    intro x h1 h2
    have hx : 1 < ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact h1
    simp only [hΦ, hfD]
    rw [← (hA x hx).tsum_eq]
    exact hAD x h1 h2
  obtain ⟨Ψ, hΨd, hΨA, hΨC, hΨD⟩ := exists_glue hΦd hCd hDd hAD' hCD
  refine residue_of_glue hs0 ht0 hq0 hΨd (fun ζ hζ => ?_) (fun ζ h0 h1 => ?_)
    (fun r h0 h1 => ?_) a ℓ
  · rw [hΨA ζ hζ]; exact hA ζ hζ
  · rw [hΨC ζ h0 h1]; exact (hT ζ h0 h1).hasSum
  · have h11 : 1 + r ≠ 1 := by intro h; apply h0; linear_combination h
    rw [hΨD (1 + r) h11 (by rwa [add_sub_cancel_left])]
    simp only [hfD, add_sub_cancel_left]
    exact (hQ r h0 h1).hasSum

end VOA.Classification.COne.McRaeO5b
