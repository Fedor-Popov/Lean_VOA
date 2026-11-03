/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLLocGlue

/-!
# HKL locality: assembling one function on `ℂ ∖ {0, -1}` from the four channels

Pure complex analysis.  Suppose four functions `cA, cB, cC, cD` (the product, `b`-outermost,
reversed-product and iterate channels of a four-point function in the hexagon coordinate `r`) are
holomorphic on their natural domains

* `cA` on `‖1 + r‖ > 1`, `cC` on `0 < ‖1 + r‖ < 1`, `cB` on `Re r < -1/2` (`r ≠ -1`),
  `cD` on `Re r > -1/2` (`r ≠ 0`),

and that on each open half plane `s · Im r > 0` (`s = ±1`) one holomorphic `P_s` agrees with each
of them on its domain (`HalfGlue`).  Then

  `glueFun r = cA r` (`‖1+r‖ > 1`), `cC r` (`‖1+r‖ < 1`), `cB r` (`‖1+r‖ = 1`, `Re r < -1/2`),
  `P_s r` (the two equilateral points)

is holomorphic on `ℂ ∖ {0, -1}` (`differentiableAt_glueFun`) and equals `cD` on the punctured
disc `0 < ‖r‖ < 1/4` (`glueFun_eq_D`).  Across the real axis the channels match by the identity
theorem on small discs (`eq_at_real`); the equilateral points `r = e^{±2πi/3}`, where no channel
converges, are covered by `P_±`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HKLLoc

open Filter Topology
open VOA.Huang.TensorCat.HexagonClose
open Complex

/-! ## A real-point identity lemma -/

/-- Two functions holomorphic on a disc around a real point that agree on its upper half agree
at the centre. -/
theorem eq_at_real {f g : ℂ → ℂ} {x ε : ℝ} (hε : 0 < ε)
    (hf : ∀ z ∈ Metric.ball (x : ℂ) ε, DifferentiableAt ℂ f z)
    (hg : ∀ z ∈ Metric.ball (x : ℂ) ε, DifferentiableAt ℂ g z)
    (hfg : ∀ z ∈ Metric.ball (x : ℂ) ε, 0 < z.im → f z = g z) : f x = g x := by
  have hfa : AnalyticOnNhd ℂ f (Metric.ball (x : ℂ) ε) :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt)
      Metric.isOpen_ball
  have hga : AnalyticOnNhd ℂ g (Metric.ball (x : ℂ) ε) :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt)
      Metric.isOpen_ball
  have hz₀ : (x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈
      Metric.ball (x : ℂ) ε ∩ {z : ℂ | 0 < z.im} := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      linarith
  have h := eqOn_of_convex (convex_ball _ _) hfa hga
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_im)) Set.inter_subset_left
    hz₀ (fun z hz => hfg z hz.1 hz.2)
  exact h (Metric.mem_ball_self hε)

theorem re_ball {x : ℝ} {ε : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (x : ℂ) ε) :
    x - ε < z.re ∧ z.re < x + ε := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - x)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  constructor <;> linarith [abs_lt.1 (lt_of_le_of_lt h hz)]

theorem norm_one_add_ball {x : ℝ} {ε : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (x : ℂ) ε) :
    |1 + x| - ε < ‖1 + z‖ ∧ ‖1 + z‖ < |1 + x| + ε := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have e : 1 + z = (1 + (x : ℂ)) + (z - x) := by ring
  have h1 : ‖1 + (x : ℂ)‖ = |1 + x| := by
    rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  constructor
  · have := norm_sub_le (1 + z) (z - x)
    rw [show 1 + z - (z - x) = 1 + (x : ℂ) by ring, h1] at this
    linarith
  · rw [e]
    calc ‖(1 + (x : ℂ)) + (z - x)‖ ≤ ‖1 + (x : ℂ)‖ + ‖z - x‖ := norm_add_le _ _
      _ < |1 + x| + ε := by rw [h1]; linarith

theorem real_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-! ## The glued function -/

/-- The glued function in the hexagon coordinate. -/
def glueFun (cA cB cC Pp Pm : ℂ → ℂ) (r : ℂ) : ℂ :=
  if 1 < ‖1 + r‖ then cA r else if ‖1 + r‖ < 1 then cC r else if r.re < -1 / 2 then cB r
  else if 0 < r.im then Pp r else Pm r

/-- One holomorphic function on the half plane `s · Im r > 0` matching the four channels. -/
structure HalfGlue (s : ℝ) (P cA cB cC cD : ℂ → ℂ) : Prop where
  ana : AnalyticOnNhd ℂ P (Lh s)
  eqA : ∀ r, 0 < s * r.im → 1 < ‖1 + r‖ → cA r = P r
  eqC : ∀ r, 0 < s * r.im → ‖1 + r‖ < 1 → cC r = P r
  eqB : ∀ r, 0 < s * r.im → r.re < -1 / 2 → cB r = P r
  eqD : ∀ r, 0 < s * r.im → -1 / 2 < r.re → cD r = P r

/-- The channels are holomorphic on their domains. -/
structure ChannelsHolo (cA cB cC cD : ℂ → ℂ) : Prop where
  dA : ∀ r, 1 < ‖1 + r‖ → DifferentiableAt ℂ cA r
  dC : ∀ r, 1 + r ≠ 0 → ‖1 + r‖ < 1 → DifferentiableAt ℂ cC r
  dB : ∀ r, 1 + r ≠ 0 → r.re < -1 / 2 → DifferentiableAt ℂ cB r
  dD : ∀ r, r ≠ 0 → -1 / 2 < r.re → DifferentiableAt ℂ cD r

variable {cA cB cC cD Pp Pm : ℂ → ℂ}
  (hp : HalfGlue 1 Pp cA cB cC cD) (hm : HalfGlue (-1) Pm cA cB cC cD)
  (hc : ChannelsHolo cA cB cC cD)

theorem glueFun_outside {r : ℂ} (h : 1 < ‖1 + r‖) : glueFun cA cB cC Pp Pm r = cA r := by
  rw [glueFun, if_pos h]

theorem glueFun_inside {r : ℂ} (h : ‖1 + r‖ < 1) : glueFun cA cB cC Pp Pm r = cC r := by
  rw [glueFun, if_neg (by linarith), if_pos h]

include hp in
theorem glueFun_upper {r : ℂ} (h : 0 < r.im) : glueFun cA cB cC Pp Pm r = Pp r := by
  have hs : 0 < (1 : ℝ) * r.im := by rwa [one_mul]
  unfold glueFun
  split_ifs with h1 h2 h3
  · exact hp.eqA r hs h1
  · exact hp.eqC r hs h2
  · exact hp.eqB r hs h3
  · rfl

include hm in
theorem glueFun_lower {r : ℂ} (h : r.im < 0) : glueFun cA cB cC Pp Pm r = Pm r := by
  have hs : 0 < (-1 : ℝ) * r.im := by linarith
  unfold glueFun
  split_ifs with h1 h2 h3 h4
  · exact hm.eqA r hs h1
  · exact hm.eqC r hs h2
  · exact hm.eqB r hs h3
  · exact absurd h4 (by linarith)
  · rfl

include hp hc in
theorem real_A_B {x : ℝ} (hx : x < -2) : cA x = cB x := by
  refine eq_at_real (ε := (-2 - x) / 2) (by linarith) (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz hz0 => ?_)
  · have h := (norm_one_add_ball hz).1
    rw [abs_of_neg (by linarith)] at h
    exact hc.dA z (by linarith)
  · have h := (norm_one_add_ball hz).1
    rw [abs_of_neg (by linarith)] at h
    exact hc.dB z (fun h0 => by rw [h0, norm_zero] at h; linarith)
      (by linarith [(re_ball hz).2])
  · have h := (norm_one_add_ball hz).1
    rw [abs_of_neg (by linarith)] at h
    have hs : 0 < (1 : ℝ) * z.im := by rwa [one_mul]
    rw [hp.eqA z hs (by linarith), hp.eqB z hs (by linarith [(re_ball hz).2])]

include hp hc in
theorem real_C_B {x : ℝ} (hx1 : -2 < x) (hx2 : x < -1) : cC x = cB x := by
  have hε : 0 < min (x + 2) (-1 - x) / 2 := by
    have := lt_min (show 0 < x + 2 by linarith) (show 0 < -1 - x by linarith); linarith
  have hε1 : min (x + 2) (-1 - x) / 2 ≤ (x + 2) / 2 := by
    have := min_le_left (x + 2) (-1 - x); linarith
  have hε2 : min (x + 2) (-1 - x) / 2 ≤ (-1 - x) / 2 := by
    have := min_le_right (x + 2) (-1 - x); linarith
  have key : ∀ z ∈ Metric.ball (x : ℂ) (min (x + 2) (-1 - x) / 2),
      1 + z ≠ 0 ∧ ‖1 + z‖ < 1 ∧ z.re < -1 / 2 := by
    intro z hz
    have h := norm_one_add_ball hz
    rw [abs_of_neg (by linarith)] at h
    refine ⟨fun h0 => by rw [h0, norm_zero] at h; linarith [h.1], by linarith [h.2],
      by linarith [(re_ball hz).2]⟩
  refine eq_at_real hε (fun z hz => ?_) (fun z hz => ?_) (fun z hz hz0 => ?_)
  · obtain ⟨h0, h1, -⟩ := key z hz; exact hc.dC z h0 h1
  · obtain ⟨h0, -, h2⟩ := key z hz; exact hc.dB z h0 h2
  · obtain ⟨-, h1, h2⟩ := key z hz
    have hs : 0 < (1 : ℝ) * z.im := by rwa [one_mul]
    rw [hp.eqC z hs h1, hp.eqB z hs h2]

include hp hc in
theorem real_A_D {x : ℝ} (hx : 0 < x) : cA x = cD x := by
  refine eq_at_real (ε := x / 2) (by linarith) (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz hz0 => ?_)
  · have h := (norm_one_add_ball hz).1
    rw [abs_of_pos (by linarith)] at h
    exact hc.dA z (by linarith)
  · have h := re_ball hz
    exact hc.dD z (fun h0 => by rw [h0, Complex.zero_re] at h; linarith [h.1]) (by linarith [h.1])
  · have h := (norm_one_add_ball hz).1
    rw [abs_of_pos (by linarith)] at h
    have hs : 0 < (1 : ℝ) * z.im := by rwa [one_mul]
    rw [hp.eqA z hs (by linarith), hp.eqD z hs (by linarith [(re_ball hz).1])]

include hp hc in
theorem real_C_D {x : ℝ} (hx1 : -1 / 4 < x) (hx2 : x < 0) : cC x = cD x := by
  have key : ∀ z ∈ Metric.ball (x : ℂ) (-x / 2),
      1 + z ≠ 0 ∧ ‖1 + z‖ < 1 ∧ z ≠ 0 ∧ -1 / 2 < z.re := by
    intro z hz
    have h := norm_one_add_ball hz
    rw [abs_of_pos (by linarith)] at h
    have hre := re_ball hz
    refine ⟨fun h0 => by rw [h0, norm_zero] at h; linarith [h.1], by linarith [h.2],
      fun h0 => by rw [h0, Complex.zero_re] at hre; linarith [hre.2], by linarith [hre.1]⟩
  refine eq_at_real (ε := -x / 2) (by linarith) (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz hz0 => ?_)
  · obtain ⟨h0, h1, -, -⟩ := key z hz; exact hc.dC z h0 h1
  · obtain ⟨-, -, h2, h3⟩ := key z hz; exact hc.dD z h2 h3
  · obtain ⟨-, h1, -, h3⟩ := key z hz
    have hs : 0 < (1 : ℝ) * z.im := by rwa [one_mul]
    rw [hp.eqC z hs h1, hp.eqD z hs h3]

theorem abs_one_add_eq_one {x : ℝ} (h : |1 + x| = 1) : x = 0 ∨ x = -2 := by
  rcases abs_eq (zero_le_one) |>.1 h with h1 | h1
  · left; linarith
  · right; linarith

theorem norm_one_add_real (x : ℝ) : ‖1 + (x : ℂ)‖ = |1 + x| := by
  rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]

include hp hm hc in
/-- **The glued function is holomorphic on `ℂ ∖ {0, -1}`.** -/
theorem differentiableAt_glueFun {r : ℂ} (h0 : r ≠ 0) (h1 : 1 + r ≠ 0) :
    DifferentiableAt ℂ (glueFun cA cB cC Pp Pm) r := by
  rcases lt_trichotomy r.im 0 with him | him | him
  · have hev : glueFun cA cB cC Pp Pm =ᶠ[𝓝 r] Pm := by
      filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds him] with z hz
      exact glueFun_lower hm hz
    exact (hm.ana r (by change 0 < (-1 : ℝ) * r.im; linarith)).differentiableAt
      |>.congr_of_eventuallyEq hev
  · rcases lt_trichotomy ‖1 + r‖ 1 with hn | hn | hn
    · have hev : glueFun cA cB cC Pp Pm =ᶠ[𝓝 r] cC := by
        filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_const.add continuous_id))
          continuous_const).mem_nhds hn] with z hz
        exact glueFun_inside hz
      exact (hc.dC r h1 hn).congr_of_eventuallyEq hev
    · -- the real circle point `r = -2`
      have hr : r = ((r.re : ℝ) : ℂ) := real_of_im_eq_zero him
      have hx : r.re = -2 := by
        rw [hr, norm_one_add_real] at hn
        rcases abs_one_add_eq_one hn with hx | hx
        · exact absurd (by rw [hr, hx]; simp) h0
        · exact hx
      have hrm2 : r = -2 := by rw [hr, hx]; push_cast; ring
      subst hrm2
      have hev : glueFun cA cB cC Pp Pm =ᶠ[𝓝 (-2 : ℂ)] cB := by
        filter_upwards [Metric.ball_mem_nhds (-2 : ℂ) (show (0 : ℝ) < 1 / 4 by norm_num)]
          with z hz
        have hz' : z ∈ Metric.ball ((-2 : ℝ) : ℂ) (1 / 4) := by
          simpa using hz
        have hre := re_ball hz'
        rcases lt_trichotomy z.im 0 with hzi | hzi | hzi
        · rw [glueFun_lower hm hzi]
          exact (hm.eqB z (by linarith) (by linarith [hre.2])).symm
        · have hz2 : z = ((z.re : ℝ) : ℂ) := real_of_im_eq_zero hzi
          rcases lt_trichotomy z.re (-2) with hx2 | hx2 | hx2
          · have hn2 : 1 < ‖1 + z‖ := by
              rw [hz2, norm_one_add_real, abs_of_neg (by linarith)]; linarith
            rw [glueFun_outside hn2, hz2]
            exact real_A_B hp hc hx2
          · have hz3 : z = -2 := by rw [hz2, hx2]; push_cast; ring
            subst hz3
            unfold glueFun
            rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]
          · have hn2 : ‖1 + z‖ < 1 := by
              rw [hz2, norm_one_add_real, abs_of_neg (by linarith [hre.2])]; linarith
            rw [glueFun_inside hn2, hz2]
            exact real_C_B hp hc hx2 (by linarith [hre.2])
        · rw [glueFun_upper hp hzi]
          exact (hp.eqB z (by linarith) (by linarith [hre.2])).symm
      exact (hc.dB (-2) (by norm_num) (by norm_num)).congr_of_eventuallyEq hev
    · have hev : glueFun cA cB cC Pp Pm =ᶠ[𝓝 r] cA := by
        filter_upwards [(isOpen_lt continuous_const
          (continuous_norm.comp (continuous_const.add continuous_id))).mem_nhds hn] with z hz
        exact glueFun_outside hz
      exact (hc.dA r hn).congr_of_eventuallyEq hev
  · have hev : glueFun cA cB cC Pp Pm =ᶠ[𝓝 r] Pp := by
      filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds him] with z hz
      exact glueFun_upper hp hz
    exact (hp.ana r (by change 0 < (1 : ℝ) * r.im; linarith)).differentiableAt
      |>.congr_of_eventuallyEq hev

include hp hm hc in
/-- **Near `r = 0` the glued function is the iterate channel.** -/
theorem glueFun_eq_D {r : ℂ} (h0 : r ≠ 0) (hr : ‖r‖ < 1 / 4) :
    glueFun cA cB cC Pp Pm r = cD r := by
  have hre : -1 / 2 < r.re := by
    have := Complex.abs_re_le_norm r
    linarith [neg_abs_le r.re]
  rcases lt_trichotomy r.im 0 with him | him | him
  · rw [glueFun_lower hm him]
    exact (hm.eqD r (by linarith) hre).symm
  · have hr2 : r = ((r.re : ℝ) : ℂ) := real_of_im_eq_zero him
    have habs : |r.re| < 1 / 4 := lt_of_le_of_lt (Complex.abs_re_le_norm r) hr
    rcases lt_trichotomy r.re 0 with hx | hx | hx
    · have hn : ‖1 + r‖ < 1 := by
        rw [hr2, norm_one_add_real, abs_of_pos (by linarith [abs_lt.1 habs])]; linarith
      rw [glueFun_inside hn, hr2]
      exact real_C_D hp hc (by linarith [abs_lt.1 habs]) hx
    · exact absurd (by rw [hr2, hx]; simp) h0
    · have hn : 1 < ‖1 + r‖ := by
        rw [hr2, norm_one_add_real, abs_of_pos (by linarith)]; linarith
      rw [glueFun_outside hn, hr2]
      exact real_A_D hp hc hx
  · rw [glueFun_upper hp him]
    exact (hp.eqD r (by linarith) hre).symm

end VOA.Huang.HKLLoc
