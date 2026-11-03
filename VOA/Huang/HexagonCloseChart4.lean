import VOA.Huang.HexagonCloseChart3
import VOA.Huang.CommutativityAnalytic

/-! # Hexagon closure: Möbius charts for Fuchsian equations (VOA-free), part 4

`fuchsian_halfPlane_continuation`: a formal solution `G` of a Fuchsian equation whose
coefficients are rational with poles only at `x = 1` (exactly Huang's product equations,
`Convergence.RatFuchsian 1`) is, on `|x| < 1`, the restriction of a function holomorphic on each
open half plane `s · Im x > 0`.

The half plane is covered by the Möbius charts `q_t = 2/(1 + i s t)`, `t > 0` (`|q_t - 1| = 1`,
`q_t` on the other side), each continuing `G` to the half plane `E_t = {|x| < |x - q_t|}`
(`chart_continuation`); the charts agree on overlaps by the identity theorem (they all equal `G`
near `x = 0`), and `x ∈ E_{t(x)}` for an explicit `t(x)`.
-/

noncomputable section
namespace VOA.Huang.TensorCat.HexagonClose
open Polynomial Filter Topology
open VOA.Huang.FrobeniusLog (psEval logFun halfPlane LogGood LogFuchsianEq)
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.FuchsianODE
open scoped BigOperators

/-! ## The charts -/

/-- The chart parameter `q_t = 2/(1 + i s t) = (2 - 2 i s t)/(1 + t²)`. -/
def qt (s t : ℝ) : ℂ := ⟨2 / (1 + t ^ 2), -(s * t) * (2 / (1 + t ^ 2))⟩

theorem qt_re (s t : ℝ) : (qt s t).re = 2 / (1 + t ^ 2) := rfl

theorem qt_im (s t : ℝ) : (qt s t).im = -(s * t) * (2 / (1 + t ^ 2)) := rfl

theorem qt_re_pos (s t : ℝ) : 0 < (qt s t).re := by rw [qt_re]; positivity

theorem qt_ne_zero (s t : ℝ) : qt s t ≠ 0 := by
  intro h; have := qt_re_pos s t; rw [h] at this; simp at this

theorem norm_one_sub_qt (s t : ℝ) (hs : s * s = 1) : ‖1 - qt s t‖ = 1 := by
  have hn : Complex.normSq (1 - qt s t) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, qt_re, qt_im]
    have h2 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp
    have : (s * t) ^ 2 = t ^ 2 := by rw [mul_pow, sq s, hs, one_mul]
    nlinarith [this]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, hn, Real.sqrt_one]

/-- The chart region `E_t = {|x| < |x - q_t|}`. -/
def Et (s t : ℝ) : Set ℂ := {x | ‖x‖ < ‖x - qt s t‖}

theorem Et_eq (s t : ℝ) (hs : s * s = 1) :
    Et s t = {x : ℂ | x.re - t * (s * x.im) < 1} := by
  ext x
  simp only [Et, Set.mem_setOf_eq]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, qt_re, qt_im]
  set a : ℝ := 2 / (1 + t ^ 2) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hst : (s * t) ^ 2 = t ^ 2 := by rw [mul_pow, sq s, hs, one_mul]
  have haa : a * a + (s * t * a) * (s * t * a) = 2 * a := by
    rw [ha]; field_simp; nlinarith [hst]
  constructor
  · intro h
    nlinarith [haa]
  · intro h
    nlinarith [haa]

theorem isOpen_Et (s t : ℝ) : IsOpen (Et s t) :=
  isOpen_lt continuous_norm (continuous_id.sub continuous_const).norm

theorem convex_Et (s t : ℝ) (hs : s * s = 1) : Convex ℝ (Et s t) := by
  rw [Et_eq s t hs]
  exact convex_halfSpace_lt (f := fun x : ℂ => x.re - t * (s * x.im))
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩ 1

/-- The covering parameter `t(x)`. -/
def tOf (s : ℝ) (x : ℂ) : ℝ := max 1 ((x.re - 1) / (s * x.im) + 1)

theorem mem_Et_tOf {s : ℝ} (hs : s * s = 1) {x : ℂ} (hx : 0 < s * x.im) :
    x ∈ Et s (tOf s x) := by
  rw [Et_eq s _ hs]
  change x.re - tOf s x * (s * x.im) < 1
  have h1 : (x.re - 1) / (s * x.im) + 1 ≤ tOf s x := le_max_right _ _
  have h2 : (x.re - 1) / (s * x.im) * (s * x.im) = x.re - 1 := div_mul_cancel₀ _ hx.ne'
  nlinarith

theorem tOf_pos (s : ℝ) (x : ℂ) : 0 < tOf s x := lt_of_lt_of_le one_pos (le_max_left _ _)

/-! ## One chart in the `x` coordinate -/

/-- The Möbius coordinate `v = x/(x - q)`. -/
def vOf (q x : ℂ) : ℂ := x / (x - q)

theorem chartX_vOf {q x : ℂ} (hq : q ≠ 0) (hxq : x ≠ q) : chartX q (vOf q x) = x := by
  have hxq' : x - q ≠ 0 := sub_ne_zero.2 hxq
  have h1 : 1 - vOf q x = -q / (x - q) := by rw [vOf]; field_simp; ring
  rw [chartX, h1, vOf]
  field_simp

theorem vOf_mem_slitPlane {s t : ℝ} (hs : s * s = 1) (ht : 0 < t) {x : ℂ} (hx : 0 < s * x.im) :
    vOf (qt s t) x ∈ Complex.slitPlane := by
  set q := qt s t with hq
  set a : ℝ := 2 / (1 + t ^ 2) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hqre : q.re = a := rfl
  have hqim : q.im = -(s * t) * a := rfl
  -- `s · Im q < 0`
  have hsq : s * q.im < 0 := by
    rw [hqim, show s * (-(s * t) * a) = -((s * s) * t * a) by ring, hs, one_mul]
    have : 0 < t * a := mul_pos ht ha0
    linarith
  have hxq : x - q ≠ 0 := by
    intro h; rw [sub_eq_zero] at h
    rw [h] at hx; linarith
  have hn : 0 < Complex.normSq (x - q) := Complex.normSq_pos.2 hxq
  have him : (vOf q x).im = (x.re * q.im - x.im * q.re) / Complex.normSq (x - q) := by
    rw [vOf, Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
    field_simp; ring
  have hre : (vOf q x).re = (Complex.normSq x - (x.re * q.re + x.im * q.im)) /
      Complex.normSq (x - q) := by
    rw [vOf, Complex.div_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
    field_simp; ring
  by_cases h0 : (vOf q x).im = 0
  · left
    rw [hre]
    refine div_pos ?_ hn
    rw [him, div_eq_zero_iff, or_iff_left hn.ne'] at h0
    -- `x.re (s Im q) = (s Im x) Re q > 0`, so `x.re < 0`
    have h1 : x.re * (s * q.im) = (s * x.im) * q.re := by linear_combination s * h0
    have hxre : x.re < 0 := by
      by_contra hc
      push Not at hc
      have : x.re * (s * q.im) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hsq.le
      have : 0 < (s * x.im) * q.re := mul_pos hx (by rw [hqre]; exact ha0)
      linarith
    have h2 : x.im * q.im < 0 := by
      have : (s * x.im) * (s * q.im) < 0 := mul_neg_of_pos_of_neg hx hsq
      have e : (s * x.im) * (s * q.im) = (s * s) * (x.im * q.im) := by ring
      rw [e, hs, one_mul] at this; exact this
    have h3 : x.re * q.re < 0 := mul_neg_of_neg_of_pos hxre (by rw [hqre]; exact ha0)
    have := Complex.normSq_nonneg x
    linarith
  · exact Or.inr h0

theorem norm_vOf_lt_one {q x : ℂ} (hx : ‖x‖ < ‖x - q‖) : ‖vOf q x‖ < 1 := by
  rw [vOf, norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) hx)]; exact hx

end VOA.Huang.TensorCat.HexagonClose

/-! ## One chart, and the gluing -/

namespace VOA.Huang.TensorCat.HexagonClose
open VOA.Huang.FrobeniusLog (psEval halfPlane)
open VOA.Huang.FuchsianODE
open Filter Topology

/-- The identity theorem on a convex open set, from an open nonempty piece (VOA-free copy). -/
theorem eqOn_of_convex' {f g : ℂ → ℂ} {U O : Set ℂ} (hUc : Convex ℝ U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hO : IsOpen O) (hOU : O ⊆ U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ O) (hfg : Set.EqOn f g O) : Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hUc.isPreconnected (hOU hz₀)
    (Filter.eventuallyEq_of_mem (hO.mem_nhds hz₀) hfg)

/-- The open half plane `s · Im x > 0`. -/
def Lhs (s : ℝ) : Set ℂ := {x | 0 < s * x.im}

theorem isOpen_Lhs (s : ℝ) : IsOpen (Lhs s) :=
  isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)

theorem convex_Lhs (s : ℝ) : Convex ℝ (Lhs s) :=
  convex_halfSpace_gt (f := fun x : ℂ => s * x.im) ⟨fun x y => by simp; ring,
    fun c x => by simp; ring⟩ 0

theorem psEval_analyticOnNhd {G : PowerSeries ℂ} (hG : G ∈ SubexpPS) :
    AnalyticOnNhd ℂ (psEval G) (Metric.ball 0 1) := by
  have := VOA.Huang.CommutativityTarget.analyticOnNhd_tsum_pow (fun k => PowerSeries.coeff k G)
    (fun r hr0 hr1 => by
      have h := summable_of_subexponential (fun n => norm_nonneg _) (mem_subexpPS.mp hG)
        hr0.le hr1
      exact h)
  exact this

/-- **One chart in the `x` coordinate.** -/
theorem chart_x {lam : ℂ} {s₀ b : ℕ} {c : ℕ → PowerSeries ℂ} {p : ℕ → Polynomial ℂ}
    (hcp : ∀ i < s₀, (1 - PowerSeries.X) ^ b * c i = (p i : PowerSeries ℂ)) {G : PowerSeries ℂ}
    (hG : FuchsianEq lam s₀ c G) {s t : ℝ} (hs : s * s = 1) (ht : 0 < t) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (Et s t ∩ Lhs s) ∧
      ∃ ε > 0, ∀ x ∈ Lhs s, ‖x‖ < ε → Ψ x = psEval G x := by
  set q := qt s t with hq
  have hq0 : q ≠ 0 := qt_ne_zero s t
  have hq1 : ‖1 - q‖ ≤ 1 := (norm_one_sub_qt s t hs).le
  obtain ⟨Gh, hGh, hGeq⟩ := chart_continuation hcp hG hq0 hq1
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  refine ⟨fun x => Gh (Complex.log (vOf q x)), fun x hx => ?_, ‖q‖ / (4 + 4 * ‖q‖),
    by positivity, fun x hx hxε => ?_⟩
  · have hxE : ‖x‖ < ‖x - q‖ := hx.1
    have hx0 : x ≠ 0 := by
      intro h; have := hx.2; rw [h] at this; change 0 < s * (0 : ℂ).im at this; simp at this
    have hxq : x - q ≠ 0 := by
      intro h; rw [h, norm_zero] at hxE; exact absurd hxE (not_lt.2 (norm_nonneg _))
    have hslit := vOf_mem_slitPlane hs ht hx.2
    have hv0 : vOf q x ≠ 0 := div_ne_zero hx0 hxq
    have hlog : (Complex.log (vOf q x)).re < 0 := by
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.2 hv0) (norm_vOf_lt_one hxE)
    have hd1 : DifferentiableAt ℂ (vOf q) x :=
      differentiableAt_id.div (differentiableAt_id.sub_const q) hxq
    exact ((hGh.differentiableAt (VOA.Huang.FrobeniusLog.isOpen_halfPlane.mem_nhds hlog)).comp x
      (hd1.clog hslit)).differentiableWithinAt
  · have hx0 : x ≠ 0 := by
      intro h; have := hx; rw [h] at this; change 0 < s * (0 : ℂ).im at this; simp at this
    have hε4 : ‖q‖ / (4 + 4 * ‖q‖) ≤ ‖q‖ / 4 :=
      div_le_div_of_nonneg_left hqn.le (by norm_num) (by linarith)
    have hxq : ‖q‖ / 2 ≤ ‖x - q‖ := by
      have := norm_sub_norm_le q x
      rw [norm_sub_rev] at this
      linarith
    have hxq0 : x - q ≠ 0 := by
      intro h; rw [h, norm_zero] at hxq; linarith
    have hv0 : vOf q x ≠ 0 := div_ne_zero hx0 hxq0
    have hvsmall : ‖vOf q x‖ < 1 / (2 + 2 * ‖q‖) := by
      rw [vOf, norm_div, div_lt_iff₀ (by linarith)]
      calc ‖x‖ < ‖q‖ / (4 + 4 * ‖q‖) := hxε
        _ = 1 / (2 + 2 * ‖q‖) * (‖q‖ / 2) := by field_simp; ring
        _ ≤ 1 / (2 + 2 * ‖q‖) * ‖x - q‖ := by gcongr
    have hlog : (Complex.log (vOf q x)).re < -chartM q := by
      rw [Complex.log_re, chartM, ← Real.log_inv, inv_eq_one_div]
      exact Real.log_lt_log (norm_pos_iff.2 hv0) hvsmall
    change Gh (Complex.log (vOf q x)) = _
    rw [hGeq _ hlog, Complex.exp_log hv0, chartX_vOf hq0 (sub_ne_zero.1 hxq0)]

/-- **Half-plane continuation of Fuchsian solutions.** A formal solution `G` of a Fuchsian
equation whose coefficients are rational with poles only at `x = 1` is, on `|x| < 1`, the
restriction of a function holomorphic on each open half plane `s · Im x > 0`. -/
theorem fuchsian_halfPlane_continuation {lam : ℂ} {s₀ b : ℕ} {c : ℕ → PowerSeries ℂ}
    {p : ℕ → Polynomial ℂ}
    (hcp : ∀ i < s₀, (1 - PowerSeries.X) ^ b * c i = (p i : PowerSeries ℂ)) {G : PowerSeries ℂ}
    (hG : FuchsianEq lam s₀ c G) {s : ℝ} (hs : s * s = 1) :
    ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Lhs s) ∧
      ∀ x ∈ Lhs s, ‖x‖ < 1 → Ψ x = psEval G x := by
  have hc : ∀ i < s₀, c i ∈ SubexpPS := fun i hi =>
    mem_subexpPS_of_mul_eq' (a := 1) (by simp) (by simpa using hcp i hi)
  have hGsub : G ∈ SubexpPS := mem_subexpPS.2 (subexponential_of_fuchsianEq hc hG)
  choose! Ψt hΨd ε hε hΨeq using fun (t : ℝ) (ht : 0 < t) => chart_x hcp hG hs ht
  -- a point near `0` in every chart
  have hpt : ∀ η : ℝ, 0 < η → ∀ t : ℝ, 0 < t →
      (((s * η : ℝ) : ℂ) * Complex.I) ∈ Et s t ∩ Lhs s := by
    intro η hη t ht
    have him : (((s * η : ℝ) : ℂ) * Complex.I).im = s * η := by simp
    have hre : (((s * η : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    refine ⟨?_, ?_⟩
    · rw [Et_eq s t hs]
      change _ - t * (s * _) < 1
      rw [him, hre, ← mul_assoc s s, hs, one_mul]
      nlinarith
    · change 0 < s * _
      rw [him, ← mul_assoc, hs, one_mul]; exact hη
  have hnorm : ∀ η : ℝ, 0 < η → ‖(((s * η : ℝ) : ℂ) * Complex.I)‖ = η := by
    intro η hη
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hη]
    have : |s| = 1 := by
      have h := congrArg abs hs
      rw [abs_mul, abs_one] at h
      nlinarith [abs_nonneg s]
    rw [this, one_mul]
  -- consistency of the charts
  have hcons : ∀ t t' : ℝ, 0 < t → 0 < t' → Set.EqOn (Ψt t) (Ψt t')
      (Et s t ∩ Et s t' ∩ Lhs s) := by
    intro t t' ht ht'
    set η : ℝ := min (ε t) (ε t') / 2 with hη
    have hη0 : 0 < η := by rw [hη]; have := lt_min (hε t ht) (hε t' ht'); positivity
    have hηt : η < ε t := by rw [hη]; have := min_le_left (ε t) (ε t'); linarith [hε t ht]
    have hηt' : η < ε t' := by rw [hη]; have := min_le_right (ε t) (ε t'); linarith [hε t' ht']
    have hU : IsOpen (Et s t ∩ Et s t' ∩ Lhs s) :=
      ((isOpen_Et s t).inter (isOpen_Et s t')).inter (isOpen_Lhs s)
    refine eqOn_of_convex' (((convex_Et s t hs).inter (convex_Et s t' hs)).inter (convex_Lhs s))
      (((hΨd t ht).mono (fun x hx => ⟨hx.1.1, hx.2⟩)).analyticOnNhd hU)
      (((hΨd t' ht').mono (fun x hx => ⟨hx.1.2, hx.2⟩)).analyticOnNhd hU)
      (O := Et s t ∩ Et s t' ∩ Lhs s ∩ Metric.ball 0 η) (hU.inter Metric.isOpen_ball)
      Set.inter_subset_left (z₀ := (((s * (η / 2) : ℝ) : ℂ) * Complex.I)) ⟨⟨⟨(hpt _ (by
        positivity) t ht).1, (hpt _ (by positivity) t' ht').1⟩, (hpt _ (by positivity) t ht).2⟩,
        by rw [Metric.mem_ball, dist_zero_right, hnorm _ (by positivity)]; linarith⟩ ?_
    intro x ⟨⟨⟨_, _⟩, hxL⟩, hxb⟩
    rw [Metric.mem_ball, dist_zero_right] at hxb
    rw [hΨeq t ht x hxL (by linarith), hΨeq t' ht' x hxL (by linarith)]
  refine ⟨fun x => Ψt (tOf s x) x, fun x₀ hx₀ => ?_, fun x hx hx1 => ?_⟩
  · set t₀ := tOf s x₀
    have ht₀ : 0 < t₀ := tOf_pos s x₀
    have hN : IsOpen (Et s t₀ ∩ Lhs s) := (isOpen_Et s t₀).inter (isOpen_Lhs s)
    have hx₀N : x₀ ∈ Et s t₀ ∩ Lhs s := ⟨mem_Et_tOf hs hx₀, hx₀⟩
    have hev : (fun x => Ψt (tOf s x) x) =ᶠ[𝓝 x₀] Ψt t₀ := by
      refine Filter.eventually_of_mem (hN.mem_nhds hx₀N) fun x hx => ?_
      exact hcons (tOf s x) t₀ (tOf_pos s x) ht₀ ⟨⟨mem_Et_tOf hs hx.2, hx.1⟩, hx.2⟩
    exact (((hΨd t₀ ht₀).analyticOnNhd hN) x₀ hx₀N).congr hev.symm
  · set t := tOf s x
    have ht : 0 < t := tOf_pos s x
    have hU : IsOpen (Et s t ∩ Lhs s ∩ Metric.ball 0 1) :=
      ((isOpen_Et s t).inter (isOpen_Lhs s)).inter Metric.isOpen_ball
    set η : ℝ := min (ε t) 1 / 2 with hη
    have hη0 : 0 < η := by rw [hη]; have := lt_min (hε t ht) one_pos; positivity
    have hηt : η < ε t := by rw [hη]; have := min_le_left (ε t) 1; linarith [hε t ht]
    have hη1 : η < 1 := by rw [hη]; have := min_le_right (ε t) 1; linarith
    have heq := eqOn_of_convex' (((convex_Et s t hs).inter (convex_Lhs s)).inter
      (convex_ball 0 1))
      (((hΨd t ht).mono Set.inter_subset_left).analyticOnNhd hU)
      ((psEval_analyticOnNhd hGsub).mono Set.inter_subset_right)
      (O := Et s t ∩ Lhs s ∩ Metric.ball 0 η) (((isOpen_Et s t).inter (isOpen_Lhs s)).inter
        Metric.isOpen_ball)
      (fun y hy => ⟨hy.1, by
        have := hy.2; rw [Metric.mem_ball] at this ⊢; linarith⟩)
      (z₀ := (((s * (η / 2) : ℝ) : ℂ) * Complex.I)) ⟨(hpt _ (by positivity) t ht), by
        rw [Metric.mem_ball, dist_zero_right, hnorm _ (by positivity)]; linarith⟩
      (fun y hy => by
        have hyb := hy.2
        rw [Metric.mem_ball, dist_zero_right] at hyb
        exact hΨeq t ht y hy.1.2 (by linarith))
    exact heq ⟨⟨mem_Et_tOf hs hx, hx⟩, by rw [Metric.mem_ball, dist_zero_right]; exact hx1⟩

end VOA.Huang.TensorCat.HexagonClose
