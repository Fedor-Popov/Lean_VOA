/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLLocSetup

/-!
# HKL locality, gluing: the four expansions of `⟨f, Y_W(a, 1+r) Y_W(b, 1) c⟩` on a half plane

Fix an algebra object `(A, μ)` (commutative, associative, trivial twist) in the ordinary modules
of a strongly rational `V`, and an integral four-point test `d = (a, b, c; f)`.  In the hexagon
coordinate `r` (`a` at `1 + r`, `b` at `1`, `c` at `0`) the four **single-valued** channels are

* `chA r = prodL (prodOp μ) d (log(1+r))` — the product `Y_W(a)Y_W(b)c`, `‖1+r‖ > 1`;
* `chC r = (1+r)^{δ-α-β-γ} prodL (prodOp μ) d.swapM (log(1/(1+r)))` — the reversed product
  `Y_W(b)Y_W(a)c`, `‖1+r‖ < 1`;
* `chB r` — the product with `b` outermost, re-expanded around `a` (`Re r < -1/2`);
* `chD r = (1+r)^{δ-α-β-γ} iterL (iterOp μ) d.swapM (log(-r/(1+r)))` — the iterate
  `Y_W(Y_W(b, ·)a, ·)c` (`Re r > -1/2`, a pole of bounded order at `r = 0`).

`exists_halfPlane_glue`: on each open half plane `s · Im r > 0` (`s = ±1`) there is **one**
holomorphic function equal to all four channels on their domains.  This is the library's hexagon
gluing (`glue_AB`, `glue_BPhi`, `glue_BC`, `glue_CD`, `productHalfPlaneContinuation_pbw`)
specialised to `K = M = iterOp μ`, `G = Gc = prodOp μ` — legitimate because `μ` is associative
(`iterate_eq_product`) and commutative for both FHL phases (`restrict_braiding_prodOp`,
`skewP_iterOp`) — together with the single-valuedness of every channel (trivial twist).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLLoc

open CategoryTheory Filter Topology
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose VOA.Huang.HKLExt
open VOA.Huang.BraidingSkew
open Complex

universe u

/-! ## Geometry: the outside of the unit disc around `-1` in a half plane is preconnected -/

/-- The region `{s Im r > 0, ‖1 + r‖ > 1}`. -/
def Outside (s : ℝ) : Set ℂ := {r | 0 < s * r.im ∧ 1 < ‖1 + r‖}

theorem isOpen_outside (s : ℝ) : IsOpen (Outside s) :=
  (isOpen_lt continuous_const (continuous_const.mul continuous_im)).inter
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_const.add continuous_id)))

/-- `{s Im r > 0, ‖1 + r‖ > 1}` is preconnected (polar coordinates around `-1`). -/
theorem isPreconnected_outside {s : ℝ} (hs : s = 1 ∨ s = -1) : IsPreconnected (Outside s) := by
  set φ : ℝ × ℝ → ℂ := fun q => -1 + (q.1 : ℂ) * Complex.exp (((s * q.2 : ℝ) : ℂ) * Complex.I)
    with hφ
  have hcont : Continuous φ := by
    refine continuous_const.add ?_
    refine (Complex.continuous_ofReal.comp continuous_fst).mul ?_
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_snd)).mul continuous_const)
  have hS : _root_.IsPreconnected (Set.Ioi (1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi) :=
    isPreconnected_Ioi.prod isPreconnected_Ioo
  have heq : Outside s = φ '' (Set.Ioi (1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi) := by
    ext r
    constructor
    · rintro ⟨him, hn⟩
      have him1 : 0 < s * (1 + r).im := by simpa using him
      have harg := sign_arg_mem hs him1
      refine ⟨(‖1 + r‖, s * Complex.arg (1 + r)), ⟨hn, harg.1, harg.2⟩, ?_⟩
      simp only [hφ]
      rw [show s * (s * Complex.arg (1 + r)) = Complex.arg (1 + r) by
        rw [← mul_assoc, sign_cases hs, one_mul], Complex.norm_mul_exp_arg_mul_I]
      ring
    · rintro ⟨⟨ρ, θ⟩, ⟨hρ, hθ0, hθ1⟩, rfl⟩
      have hρ : 1 < ρ := hρ
      have e1 : 1 + φ (ρ, θ) = (ρ : ℂ) * Complex.exp (((s * θ : ℝ) : ℂ) * Complex.I) := by
        simp only [hφ]; ring
      refine ⟨?_, ?_⟩
      · have : (φ (ρ, θ)).im = (1 + φ (ρ, θ)).im := by simp
        rw [this, e1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
        have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ1
        rcases hs with rfl | rfl
        · simp only [one_mul]; positivity
        · simp only [neg_one_mul, Real.sin_neg]; nlinarith
      · rw [e1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
        exact hρ
  rw [heq]
  exact hS.image _ hcont.continuousOn

/-! ## The four channels -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable (F : FusionChoice V) {A : Ordinary V} (μ : tensorObj F A A ⟶ A)
  (d : FourPointTest A A A A)

/-- The product channel `⟨f, Y_W(a, 1+r) Y_W(b, 1) c⟩`. -/
def chA (r : ℂ) : ℂ := prodL F (prodOp F μ) d (Complex.log (1 + r))

/-- The reversed-product channel `⟨f, Y_W(b, 1) Y_W(a, 1+r) c⟩`. -/
def chC (r : ℂ) : ℂ := ED d r * prodL F (prodOp F μ) d.swapM (Complex.log (1 / (1 + r)))

/-- The channel with `b` outermost, re-expanded around `a`. -/
def chB (N : ℕ) (r : ℂ) : ℂ :=
  Complex.exp ((d.δ - d.α - d.β - d.γ) * Complex.log (-(1 + r))) *
    ∑ j ∈ Finset.range N, sc j * prodL F (prodOp F μ) (d.lowerK j) (Complex.log (r / (1 + r)))

/-- The iterate channel `⟨f, Y_W(Y_W(b, -r)a, 1+r) c⟩`. -/
def chD (r : ℂ) : ℂ := ED d r * iterL F (iterOp F μ) d.swapM (Complex.log (-(r / (1 + r))))

/-! ## Holomorphy of the channels (single-valuedness) -/

variable {F μ d}
variable (hV : StronglyRational V) (htw : (twistIso A).hom = 𝟙 A) (hd : IntTest d)
include hV htw hd

theorem ED_eq : ∃ n : ℤ, ∀ r' : ℂ, 1 + r' ≠ 0 →
    ED d r' = (1 + r') ^ n := by
  obtain ⟨n, hn⟩ := hd.total
  exact ⟨n, fun r' h' => by rw [ED, hn, exp_int_mul_log n h']⟩

theorem differentiableAt_ED {r : ℂ} (h1 : 1 + r ≠ 0) : DifferentiableAt ℂ (ED d) r := by
  obtain ⟨n, hn⟩ := ED_eq hV htw hd
  have hev : ED d =ᶠ[𝓝 r] fun r' => (1 + r') ^ n := by
    filter_upwards [(by fun_prop : Continuous fun r' : ℂ => 1 + r').continuousAt.eventually_ne
      h1] with r' hr'
    exact hn r' hr'
  exact ((by fun_prop : DifferentiableAt ℂ (fun r' : ℂ => 1 + r') r).zpow
    (Or.inl h1)).congr_of_eventuallyEq hev

theorem differentiableAt_chA {r : ℂ} (h : 1 < ‖1 + r‖) : DifferentiableAt ℂ (chA F μ d) r :=
  (differentiableAt_prodL_log htw hV hd h).comp r ((differentiableAt_const 1).add differentiableAt_id)

theorem differentiableAt_chC {r : ℂ} (h0 : 1 + r ≠ 0) (h : ‖1 + r‖ < 1) :
    DifferentiableAt ℂ (chC F μ d) r := by
  have hζ : 1 < ‖1 / (1 + r)‖ := by
    rw [norm_div, norm_one, one_lt_div (norm_pos_iff.2 h0)]; exact h
  refine (differentiableAt_ED hV htw hd h0).mul ?_
  exact (differentiableAt_prodL_log htw hV hd.swapM hζ).comp r
    ((differentiableAt_const 1).div ((differentiableAt_const 1).add differentiableAt_id) h0)

theorem differentiableAt_chB (N : ℕ) {r : ℂ} (h0 : 1 + r ≠ 0) (hre : r.re < -1 / 2) :
    DifferentiableAt ℂ (chB F μ d N) r := by
  obtain ⟨n, hn⟩ := hd.total
  have hm0 : -(1 + r) ≠ 0 := neg_ne_zero.2 h0
  have hE : DifferentiableAt ℂ
      (fun r : ℂ => Complex.exp ((d.δ - d.α - d.β - d.γ) * Complex.log (-(1 + r)))) r := by
    have hev : (fun r : ℂ => Complex.exp ((d.δ - d.α - d.β - d.γ) * Complex.log (-(1 + r))))
        =ᶠ[𝓝 r] fun r' => (-(1 + r')) ^ n := by
      filter_upwards [(by fun_prop : Continuous fun r' : ℂ => -(1 + r')).continuousAt.eventually_ne
        hm0] with r' hr'
      rw [hn, exp_int_mul_log n hr']
    exact ((by fun_prop : DifferentiableAt ℂ (fun r' : ℂ => -(1 + r')) r).zpow
      (Or.inl hm0)).congr_of_eventuallyEq hev
  refine hE.mul (DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_)
  have hζ : 1 < ‖r / (1 + r)‖ := by
    rw [norm_div, one_lt_div (norm_pos_iff.2 h0)]; exact norm_one_add_lt_norm hre
  exact (differentiableAt_prodL_log htw hV (hd.lowerK j) hζ).comp r
    (differentiableAt_id.div ((differentiableAt_const 1).add differentiableAt_id) h0)

theorem differentiableAt_chD {r : ℂ} (h0 : r ≠ 0) (hre : -1 / 2 < r.re) :
    DifferentiableAt ℂ (chD F μ d) r := by
  have hlt := norm_lt_norm_one_add hre
  have h1 : 1 + r ≠ 0 := fun h => by rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg r))
  have hρ0 : -(r / (1 + r)) ≠ 0 := neg_ne_zero.2 (div_ne_zero h0 h1)
  have hρ : ‖-(r / (1 + r))‖ < 1 := by
    rw [norm_neg, norm_div, div_lt_one (norm_pos_iff.2 h1)]; exact hlt
  refine (differentiableAt_ED hV htw hd h1).mul ?_
  exact (differentiableAt_iterL_log htw hV hd.swapM hρ0 hρ).comp r
    (differentiableAt_id.div ((differentiableAt_const 1).add differentiableAt_id) h1).neg

omit hV htw hd

/-! ## The gluing on one half plane -/

variable (hcomm : (braiding F A A).hom ≫ μ = μ)
  (hassoc : tensorHom F μ (𝟙 A) ≫ μ =
    (evalAssoc F (ordinaryFourPointInput_pbw F hV) A A A).hom ≫ tensorHom F (𝟙 A) μ ≫ μ)

include hV htw hd hcomm hassoc in
/-- **One holomorphic function on each half plane.** For `s = ±1` (with the matching FHL
phase) there is `P`, holomorphic on `s · Im r > 0`, equal there to each of the four channels on
its domain. -/
theorem exists_halfPlane_glue {s : ℝ} (hs : s = 1 ∨ s = -1) {p : Phase} (hp : IsFHLPhase p)
    (hκ : ∀ n, p.c n = Complex.exp (kap s * (n + 1))) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → A.isMod.weight (d.δ - j) = ⊥) :
    ∃ P : ℂ → ℂ, AnalyticOnNhd ℂ P (Lh s) ∧
      (∀ r, 0 < s * r.im → 1 < ‖1 + r‖ → chA F μ d r = P r) ∧
      (∀ r, 0 < s * r.im → ‖1 + r‖ < 1 → chC F μ d r = P r) ∧
      (∀ r, 0 < s * r.im → r.re < -1 / 2 → chB F μ d N r = P r) ∧
      (∀ r, 0 < s * r.im → -1 / 2 < r.re → chD F μ d r = P r) := by
  set K : IterateSpace F A A A A := iterOp F μ with hKdef
  set G : ProductSpace F A A A A := prodOp F μ with hGdef
  have hK : iterateEvaluation F K = productEvaluation F G := iterate_eq_product hV hassoc
  set Gc := restrictInputs (𝟙 A) (braidingP p F A A).hom G with hGc
  have hGcG : Gc = G := restrict_braiding_prodOp hcomm hp
  have hM : iterateEvaluation F K = productEvaluation F Gc := by rw [hGcG]; exact hK
  have hT := innerBraidTranslation_of_phase F hV p hs hκ
  choose Φ hΦa hΦ using fun j : ℕ =>
    productHalfPlaneContinuation_pbw F hV A A A A G (d.lowerK j) s hs
  have hPhi : ∀ U : Set ℂ, IsOpen U → U ⊆ Lh s → AnalyticOnNhd ℂ (PhiT s d N Φ) U :=
    fun U hU hUL => DifferentiableOn.analyticOnNhd (fun r hr' =>
      (differentiableAt_PhiT hs d N hΦa (hUL hr')).differentiableWithinAt) hU
  -- S3: `fA = PhiT` on `{s Im r > 1}`
  have S3 : Set.EqOn (fA F s K d N) (PhiT s d N Φ) {r | 1 < s * r.im} := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-3) 2
    refine eqOn_of_convex (convex_sim_gt s 1) ?_ ?_
      ((isOpen_re_lt (-2)).inter (isOpen_sim_gt s 1)) Set.inter_subset_right
      (z₀ := (-3 : ℝ) + ((2 * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_) (isOpen_sim_gt s 1)
      have hr' : 1 < s * r.im := hr'
      exact (differentiableAt_fA F hV s K d N (one_lt_norm_one_add_of_sim hs hr')
        (mem_slitPlane_of_sim hs (by rw [sim_one_add]; linarith))).differentiableWithinAt
    · exact hPhi _ (isOpen_sim_gt s 1) fun r hr' => by
        change 0 < s * r.im; have : 1 < s * r.im := hr'; linarith
    · simp only [Set.mem_setOf_eq]; rw [hz1]; norm_num
    · simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hre, him⟩
      have hre : r.re < -2 := hre
      have him : 1 < s * r.im := him
      rw [glue_AB F hV hs K G hK d N hre (by linarith),
        glue_BPhi F hs G d N (hΦ ·) (by linarith) (by linarith)]
  -- G1: `fA = PhiT` on the whole outside region
  have G1 : Set.EqOn (fA F s K d N) (PhiT s d N Φ) (Outside s) := by
    have hfA : AnalyticOnNhd ℂ (fA F s K d N) (Outside s) := by
      refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_) (isOpen_outside s)
      exact (differentiableAt_fA F hV s K d N hr'.2
        (mem_slitPlane_of_sim hs (by rw [sim_one_add]; exact hr'.1))).differentiableWithinAt
    have hP := hPhi _ (isOpen_outside s) fun r hr' => hr'.1
    obtain ⟨hz1, hz2⟩ := point_mem s hs 0 2
    have hz : ((0 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I ∈ {r : ℂ | 1 < s * r.im} := by
      simp only [Set.mem_setOf_eq]; rw [hz2]; norm_num
    have hzO : ((0 : ℝ) : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I ∈ Outside s :=
      ⟨by rw [hz2]; norm_num, one_lt_norm_one_add_of_sim hs (by rw [hz2]; norm_num)⟩
    refine hfA.eqOn_of_preconnected_of_eventuallyEq hP (isPreconnected_outside hs) hzO ?_
    filter_upwards [(isOpen_sim_gt s 1).mem_nhds hz] with r hr
    exact S3 hr
  -- S6: `fC = PhiT` on `{|1+r| < 1, s Im r > 0}`
  have S6 : Set.EqOn (fC F s Gc d) (PhiT s d N Φ) (Metric.ball (-1 : ℂ) 1 ∩ Lh s) := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-3 / 4) (1 / 8)
    refine eqOn_of_convex ((convex_ball _ _).inter (convex_Lh s)) ?_ ?_
      (O := Metric.ball (-3 / 4 : ℂ) (1 / 4) ∩ Lh s)
      (Metric.isOpen_ball.inter (isOpen_Lh s)) ?_
      (z₀ := ((-3 / 4 : ℝ) : ℂ) + (((1 / 8) * s : ℝ) : ℂ) * Complex.I) ⟨?_, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_)
        (Metric.isOpen_ball.inter (isOpen_Lh s))
      have hb := hr'.1
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm] at hb
      exact (differentiableAt_fC F hV hs Gc d hr'.2 hb).differentiableWithinAt
    · exact hPhi _ (Metric.isOpen_ball.inter (isOpen_Lh s)) Set.inter_subset_right
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
    · simp only [Lh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨hb, hl⟩
      have hre : r.re < -1 / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hb
        have := Complex.abs_re_le_norm (r - -3 / 4)
        have h2 : (r - -3 / 4).re = r.re + 3 / 4 := by simp; norm_num
        rw [h2] at this
        linarith [le_abs_self (r.re + 3 / 4)]
      rw [← glue_BC F hV p hs hT G d hN hb hl, glue_BPhi F hs G d N (hΦ ·) hre hl]
  -- S7: `fD = PhiT` on `{Re r > -1/2, s Im r > 0}`
  have S7 : Set.EqOn (fD F s K d) (PhiT s d N Φ) ({r | -1 / 2 < r.re} ∩ Lh s) := by
    obtain ⟨hz1, hz2⟩ := point_mem s hs (-1 / 4) (1 / 4)
    refine eqOn_of_convex ((convex_re_gt _).inter (convex_Lh s)) ?_ ?_
      (O := (Metric.ball (-1 / 2 : ℂ) (1 / 2) ∩ {r : ℂ | -1 / 2 < r.re}) ∩ Lh s)
      ((Metric.isOpen_ball.inter (isOpen_re_gt _)).inter (isOpen_Lh s))
      (fun r hr' => ⟨hr'.1.2, hr'.2⟩)
      (z₀ := ((-1 / 4 : ℝ) : ℂ) + (((1 / 4) * s : ℝ) : ℂ) * Complex.I)
      ⟨⟨?_, ?_⟩, ?_⟩ ?_
    · refine DifferentiableOn.analyticOnNhd (fun r hr' => ?_)
        ((isOpen_re_gt _).inter (isOpen_Lh s))
      have hre : -1 / 2 < r.re := hr'.1
      have him : 0 < s * r.im := hr'.2
      exact (differentiableAt_fD F hV s K d (mem_slitPlane_of_sim hs him)
        (mem_slitPlane_of_sim hs (by rwa [sim_one_add])) (norm_lt_norm_one_add hre)
        ).differentiableWithinAt
    · exact hPhi _ ((isOpen_re_gt _).inter (isOpen_Lh s)) Set.inter_subset_right
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
    · simp only [Lh, Set.mem_setOf_eq]; rw [hz2]; norm_num
    · intro r ⟨⟨hb, hre⟩, hl⟩
      have hre : -1 / 2 < r.re := hre
      have hC : r ∈ Metric.ball (-1 : ℂ) 1 ∩ Lh s := by
        refine ⟨?_, hl⟩
        rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
        calc ‖r - -1‖ = ‖(r - -1 / 2) + 1 / 2‖ := by congr 1; ring
          _ ≤ ‖r - -1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
          _ < 1 := by rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]; linarith
      rw [← glue_CD F hV hs K Gc hM d hb hre hl]
      exact S6 hC
  refine ⟨PhiT s d N Φ, hPhi _ (isOpen_Lh s) subset_rfl, ?_, ?_, ?_, ?_⟩
  · -- the product channel
    intro r him hn
    rw [← G1 ⟨him, hn⟩]
    have h10 : 1 + r ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
    have hlam : 0 < (Complex.log (1 + r)).re := by
      rw [Complex.log_re]; exact Real.log_pos hn
    have h := prodL_skewP F hV p hs hκ K d hlam
    rw [hKdef, skewP_iterOp hcomm hp] at h
    rw [chA, h, fA, EA]
    congr 1
    refine tsum_eq_sum fun j hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [iterL_lowerK_eq_zero F K d (hN j hj), mul_zero]
  · -- the reversed product channel
    intro r him hn
    have hr0 := ne_zero_of_sim hs him
    have h10 := one_add_ne_zero_of_sim hs him
    have hb : r ∈ Metric.ball (-1 : ℂ) 1 ∩ Lh s := by
      refine ⟨?_, him⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, add_comm]; exact hn
    rw [← S6 hb, fC, hGcG, one_add_exp_ellM hs hr0 h10]
    rfl
  · -- the `b`-outermost channel
    intro r him hre
    have h10 := one_add_ne_zero_of_sim hs him
    rw [← glue_BPhi F hs G d N (hΦ ·) hre him, fB, EA, one_add_exp_ellK hs h10, chB]
    congr 1
    obtain ⟨n, hn⟩ := hd.total
    rw [hn]
    refine exp_int_congr n ?_
    rw [Complex.exp_sub, exp_kap hs, Complex.exp_log h10,
      Complex.exp_log (neg_ne_zero.2 h10)]
    field_simp
  · -- the iterate channel
    intro r him hre
    have hr0 := ne_zero_of_sim hs him
    have h10 := one_add_ne_zero_of_sim hs him
    rw [← S7 ⟨hre, him⟩, fD, chD]
    congr 1
    refine iterL_congr htw hd.swapM ?_
    rw [Complex.exp_log (neg_ne_zero.2 (div_ne_zero hr0 h10)), exp_ellM hs hr0 h10]

end VOA.Huang.HKLLoc
