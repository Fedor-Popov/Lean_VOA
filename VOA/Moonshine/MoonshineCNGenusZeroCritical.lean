/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroPropertyP
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Genus zero on the abstract interface: property P including doubly critical pairs

Property P completed (blueprint `Notes/moonshine/MOON_M8_LEAN.md`): for a replicable family of
period `N > 0` satisfying the prime Hecke identity and `f = qSeriesFun (F.c k)`, **equal values are
always related by the symmetry group**: `f z = f w → ∃ γ ∈ symmetryGroup f, γ • z = w`
(`exists_mem_symmetryGroup_smul_eq`).

The case where `f′` vanishes at both points is reduced to the non-critical case
(`exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero`) by approximation: critical points are
isolated (`eventually_deriv_qSeriesExt_ne_zero`), and by the open mapping theorem there are
`z_n → z`, `w_n → w` with `f z_n = f w_n` and `f′ w_n ≠ 0`, hence `γ_n z_n = w_n` with
`γ_n ∈ symmetryGroup f`. The entries of `γ_n` are bounded (`exists_bound_entries_of_smul_eq`, from
`Im (γ τ) = Im τ / |c τ + d|²`), a subsequence converges, and the limit is a symmetry by continuity
(closedness of `symmetryGroup f`; discreteness is not needed) sending `z` to `w`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Isolated critical points and open mapping -/

section Analytic

variable {c : ℕ → ℂ}

/-- A `J`-dominated `q`-series is not locally constant at any point of `ℍ`. -/
lemma not_eventually_eq_qSeriesExt (hc : IsJDominated c) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    ¬ ∀ᶠ z in 𝓝 z₀, qSeriesExt c z = qSeriesExt c z₀ := by
  intro h
  have heq : EqOn (qSeriesExt c) (fun _ => qSeriesExt c z₀) upperHalfPlaneSet :=
    ((differentiableOn_qSeriesExt hc).analyticOnNhd
      isOpen_upperHalfPlaneSet).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_halfSpace_im_gt 0).isPreconnected hz₀ h
  obtain ⟨u, v, hu, hv, hne⟩ := qSeriesExt_exists_ne hc
  exact hne ((heq hu).trans (heq hv).symm)

/-- Critical points of a `J`-dominated `q`-series are isolated. -/
lemma eventually_deriv_qSeriesExt_ne_zero (hc : IsJDominated c) {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    ∀ᶠ u in 𝓝[≠] w₀, _root_.deriv (qSeriesExt c) u ≠ 0 := by
  have hA : AnalyticAt ℂ (_root_.deriv (qSeriesExt c)) w₀ :=
    ((differentiableOn_qSeriesExt hc).analyticOnNhd isOpen_upperHalfPlaneSet w₀ hw₀).deriv
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (h.and (isOpen_upperHalfPlaneSet.mem_nhds hw₀))
    apply not_eventually_eq_qSeriesExt hc hw₀
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hε) fun z hz => ?_
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      ((differentiableOn_qSeriesExt hc).mono fun u hu => (hball u hu).2)
      (fun u hu => (hball u hu).1) hz (Metric.mem_ball_self hε)
  · exact h

end Analytic

/-! ### Bounded entries -/

lemma abs_le_sq_add_one (t : ℝ) : |t| ≤ t ^ 2 + 1 := by
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]

/-- **Bounded entries.** For fixed `Y > 0` and `R`, the entries of real Möbius maps of determinant
one sending a point `τ` to a point `σ` with `Y ≤ Im τ, Im σ` and `‖τ‖, ‖σ‖ ≤ R` are bounded. -/
lemma exists_bound_entries_of_smul_eq {Y R : ℝ} (hY : 0 < Y) :
    ∃ B : ℝ, ∀ γ : GL (Fin 2) ℝ, γ.det.val = 1 → ∀ τ σ : ℍ, γ • τ = σ → Y ≤ τ.im → Y ≤ σ.im →
      ‖(τ : ℂ)‖ ≤ R → ‖(σ : ℂ)‖ ≤ R →
        |γ 0 0| ≤ B ∧ |γ 0 1| ≤ B ∧ |γ 1 0| ≤ B ∧ |γ 1 1| ≤ B := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = R / Y := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = (Q + 1) / Y := ⟨_, rfl⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = (Q + 1) + Bc * R := ⟨_, rfl⟩
  obtain ⟨Ba, hBa⟩ : ∃ Ba : ℝ, Ba = (R * (Q + 1) + R * (Q + 1)) / Y := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = R * (Q + 1) + R * (Q + 1) + Ba * R := ⟨_, rfl⟩
  refine ⟨max (max Ba Bb) (max Bc Bd), fun γ hdet τ σ h hτY hσY hτR hσR => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = γ 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = γ 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = γ 1 0 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = γ 1 1 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (τ : ℂ).re := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (τ : ℂ).im := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (σ : ℂ).re := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (σ : ℂ).im := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc, ← hd]
  have hyY : Y ≤ y := by rw [hy]; exact hτY
  have hvY : Y ≤ v := by rw [hv]; exact hσY
  have hy0 : 0 < y := hY.trans_le hyY
  have hv0 : 0 < v := hY.trans_le hvY
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hτR
  have hxR : |x| ≤ R := by rw [hx]; exact (Complex.abs_re_le_norm _).trans hτR
  have huR : |u| ≤ R := by rw [hu]; exact (Complex.abs_re_le_norm _).trans hσR
  have hvR : |v| ≤ R := by rw [hv]; exact (Complex.abs_im_le_norm _).trans hσR
  have hyR : y ≤ R := by rw [hy]; exact (Complex.im_le_norm _).trans hτR
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = c * x + d := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = c * y := ⟨_, rfl⟩
  have hτc : (τ : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
    rw [hx, hy]
    exact (Complex.re_add_im _).symm
  have hσc : (σ : ℂ) = (u : ℂ) + (v : ℂ) * Complex.I := by
    rw [hu, hv]
    exact (Complex.re_add_im _).symm
  have hdenEF : denom γ τ = (E : ℂ) + (F : ℂ) * Complex.I := by
    rw [denom, ← hc, ← hd, hτc, hE, hF]
    push_cast
    ring
  have hnum : num γ τ = (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) + b := by
    rw [num, ← ha, ← hb, hτc]
  have him : v = y / (E ^ 2 + F ^ 2) := by
    have h1 := im_smul_eq_div_normSq γ τ
    rw [h, hdet, abs_one, one_mul, hdenEF, Complex.normSq_add_mul_I] at h1
    rw [hv, hy]
    exact h1
  have hEF0 : 0 < E ^ 2 + F ^ 2 := by
    rcases (add_nonneg (sq_nonneg E) (sq_nonneg F)).lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, div_zero] at him
      linarith
  have hEF : E ^ 2 + F ^ 2 ≤ Q := by
    have h1 : E ^ 2 + F ^ 2 = y / v := by
      rw [eq_div_iff hv0.ne']
      rw [eq_div_iff hEF0.ne'] at him
      linarith
    rw [h1, hQ, div_le_div_iff₀ hv0 hY]
    have h2 := mul_le_mul_of_nonneg_right hyR hY.le
    have h3 := mul_le_mul_of_nonneg_left hvY hR0
    linarith
  have hFb : |F| ≤ Q + 1 := by
    have h1 := abs_le_sq_add_one F
    have h2 := sq_nonneg E
    linarith
  have hEb : |E| ≤ Q + 1 := by
    have h1 := abs_le_sq_add_one E
    have h2 := sq_nonneg F
    linarith
  have hcb : |c| ≤ Bc := by
    rw [hBc, le_div_iff₀ hY]
    have h1 : |F| = |c| * y := by rw [hF, abs_mul, abs_of_pos hy0]
    have h2 : |c| * Y ≤ |c| * y := mul_le_mul_of_nonneg_left hyY (abs_nonneg c)
    linarith
  have hdb : |d| ≤ Bd := by
    have h1 : d = E - c * x := by rw [hE]; ring
    have h2 : |c * x| ≤ Bc * R := by
      rw [abs_mul]
      exact mul_le_mul hcb hxR (abs_nonneg x) ((abs_nonneg c).trans hcb)
    rw [h1, hBd]
    have := abs_sub E (c * x)
    linarith
  -- the relation `σ (c τ + d) = a τ + b`
  have hrel : (σ : ℂ) * denom γ τ = num γ τ := by
    rw [← h, coe_smul_of_det_pos (by rw [hdet]; exact one_pos),
      div_mul_cancel₀ _ (denom_ne_zero γ τ)]
  rw [hdenEF, hnum, hσc] at hrel
  have hrelI : v * E + u * F = a * y := by
    have h1 := congrArg Complex.im hrel
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, add_zero, zero_add, sub_self] at h1
    linarith
  have hrelR : u * E - v * F = a * x + b := by
    have h1 := congrArg Complex.re hrel
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, sub_zero, add_zero, zero_add, sub_self] at h1
    linarith
  have hab : |a| ≤ Ba := by
    rw [hBa, le_div_iff₀ hY]
    have h1 : |a| * y = |v * E + u * F| := by rw [hrelI, abs_mul, abs_of_pos hy0]
    have h2 : |v * E + u * F| ≤ R * (Q + 1) + R * (Q + 1) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hvR hEb (abs_nonneg _) hR0)
        (mul_le_mul huR hFb (abs_nonneg _) hR0)
    have h3 : |a| * Y ≤ |a| * y := mul_le_mul_of_nonneg_left hyY (abs_nonneg a)
    linarith
  have hbb : |b| ≤ Bb := by
    have h1 : b = u * E - v * F - a * x := by linarith
    have h2 : |u * E| ≤ R * (Q + 1) := by
      rw [abs_mul]
      exact mul_le_mul huR hEb (abs_nonneg _) hR0
    have h3 : |v * F| ≤ R * (Q + 1) := by
      rw [abs_mul]
      exact mul_le_mul hvR hFb (abs_nonneg _) hR0
    have h4 : |a * x| ≤ Ba * R := by
      rw [abs_mul]
      exact mul_le_mul hab hxR (abs_nonneg _) ((abs_nonneg a).trans hab)
    rw [h1, hBb]
    have h5 := abs_sub (u * E - v * F) (a * x)
    have h6 := abs_sub (u * E) (v * F)
    linarith
  exact ⟨hab.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hbb.trans ((le_max_right _ _).trans (le_max_left _ _)),
    hcb.trans ((le_max_left _ _).trans (le_max_right _ _)),
    hdb.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! ### Property P -/

/-- **Equal values are related by the symmetry group** (property P). For a replicable family
of period `N > 0` satisfying the prime Hecke identity, `f z = f w` implies `γ • z = w` for some
`γ ∈ symmetryGroup f`, `f = qSeriesFun (F.c k)`. -/
theorem exists_mem_symmetryGroup_smul_eq {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N) (k : ℕ)
    (hB1 : PrimeHeckeIdentity F k) {z w : ℍ}
    (hzw : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w) :
    ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ • z = w := by
  have hc := F.isJDominated k
  by_cases hcrit : _root_.deriv (qSeriesExt (F.c k)) (z : ℂ) ≠ 0 ∨
      _root_.deriv (qSeriesExt (F.c k)) (w : ℂ) ≠ 0
  · exact exists_mem_symmetryGroup_smul_eq_of_not_both_critical hN F k hB1 hzw hcrit
  set g := qSeriesExt (F.c k) with hg
  have hgz : g z = g w := by rw [hg, qSeriesExt_coe, qSeriesExt_coe, hzw]
  have hgd := differentiableOn_qSeriesExt hc
  have hgA := hgd.analyticOnNhd isOpen_upperHalfPlaneSet
  have hz0 : 0 < (z : ℂ).im := z.im_pos
  have hw0 : 0 < (w : ℂ).im := w.im_pos
  have hopen : 𝓝 (g z) ≤ map g (𝓝 (z : ℂ)) :=
    (hgA z hz0).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_eq_qSeriesExt hc hz0)
  have hnc := eventually_deriv_qSeriesExt_ne_zero hc hw0
  have hgc : ContinuousAt g w := (hgA w hw0).continuousAt
  -- approximating pairs
  have hseq : ∀ n : ℕ, ∃ zn wn : ℂ,
      zn ∈ Metric.ball (z : ℂ) (min (1 / ((n : ℝ) + 1)) ((z : ℂ).im / 2)) ∧
      wn ∈ Metric.ball (w : ℂ) (min (1 / ((n : ℝ) + 1)) ((w : ℂ).im / 2)) ∧
      g zn = g wn ∧ _root_.deriv g wn ≠ 0 := by
    intro n
    have hrz : 0 < min (1 / ((n : ℝ) + 1)) ((z : ℂ).im / 2) :=
      lt_min (by positivity) (half_pos hz0)
    have hrw : 0 < min (1 / ((n : ℝ) + 1)) ((w : ℂ).im / 2) :=
      lt_min (by positivity) (half_pos hw0)
    have himg : g '' Metric.ball (z : ℂ) (min (1 / ((n : ℝ) + 1)) ((z : ℂ).im / 2)) ∈
        𝓝 (g w) := by
      rw [← hgz]
      exact hopen (image_mem_map (Metric.ball_mem_nhds _ hrz))
    have hpre := hgc.preimage_mem_nhds himg
    have e1 : ∀ᶠ u in 𝓝[≠] (w : ℂ),
        u ∈ g ⁻¹' (g '' Metric.ball (z : ℂ) (min (1 / ((n : ℝ) + 1)) ((z : ℂ).im / 2))) :=
      mem_nhdsWithin_of_mem_nhds hpre
    have e2 : ∀ᶠ u in 𝓝[≠] (w : ℂ),
        u ∈ Metric.ball (w : ℂ) (min (1 / ((n : ℝ) + 1)) ((w : ℂ).im / 2)) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hrw)
    obtain ⟨u, ⟨zn, hzn, hgzn⟩, hu, hdu⟩ := (e1.and (e2.and hnc)).exists
    exact ⟨zn, u, hzn, hu, hgzn, hdu⟩
  choose zs ws hzs hws hgs hds using hseq
  have hzsU : ∀ n, 0 < (zs n).im := fun n =>
    im_pos_of_mem_ball ((min_le_right _ _).trans (by linarith)) (hzs n)
  have hwsU : ∀ n, 0 < (ws n).im := fun n =>
    im_pos_of_mem_ball ((min_le_right _ _).trans (by linarith)) (hws n)
  have hlim_of : ∀ (s : ℕ → ℂ) (s₀ : ℂ) (r : ℝ),
      (∀ n : ℕ, s n ∈ Metric.ball s₀ (min (1 / ((n : ℝ) + 1)) r)) → Tendsto s atTop (𝓝 s₀) := by
    intro s s₀ r hs
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε
    refine ⟨N₀, fun n hn => ?_⟩
    have h1 : dist (s n) s₀ < 1 / ((n : ℝ) + 1) :=
      (Metric.mem_ball.mp (hs n)).trans_le (min_le_left _ _)
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    linarith
  have hzlim := hlim_of zs z _ hzs
  have hwlim := hlim_of ws w _ hws
  -- the non-critical symmetries
  have hγ : ∀ n, ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)),
      γ • (⟨zs n, hzsU n⟩ : ℍ) = ⟨ws n, hwsU n⟩ := fun n =>
    exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero hN F k hB1
      ((qSeriesExt_of_im_pos _ (hzsU n)).symm.trans ((hgs n).trans
        (qSeriesExt_of_im_pos _ (hwsU n)))) (hds n)
  choose γ hγG hγz using hγ
  have hdetn : ∀ n, (γ n).det.val = 1 := fun n => by rw [(hγG n).1]; rfl
  have hdetn' : ∀ n, γ n 0 0 * γ n 1 1 - γ n 0 1 * γ n 1 0 = 1 := fun n => by
    rw [← hdetn n, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hform : ∀ n (τ : ℍ), ((γ n • τ : ℍ) : ℂ) =
      ((γ n 0 0 : ℂ) * τ + γ n 0 1) / ((γ n 1 0 : ℂ) * τ + γ n 1 1) := fun n τ => by
    rw [coe_smul_of_det_pos (by rw [hdetn n]; exact one_pos)]
    rfl
  -- bounded entries
  set Y := min ((z : ℂ).im / 2) ((w : ℂ).im / 2) with hY
  have hY0 : 0 < Y := lt_min (half_pos hz0) (half_pos hw0)
  set R := max (‖(z : ℂ)‖ + (z : ℂ).im / 2) (‖(w : ℂ)‖ + (w : ℂ).im / 2) with hR
  obtain ⟨B, hB⟩ := exists_bound_entries_of_smul_eq (R := R) hY0
  have hball_bounds : ∀ (s₀ s : ℂ), s ∈ Metric.ball s₀ (s₀.im / 2) →
      s₀.im / 2 ≤ s.im ∧ ‖s‖ ≤ ‖s₀‖ + s₀.im / 2 := by
    intro s₀ s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have h1 := Complex.abs_im_le_norm (s - s₀)
    rw [Complex.sub_im] at h1
    have h2 := norm_sub_norm_le s s₀
    constructor
    · have := (abs_lt.mp (h1.trans_lt hs)).1
      linarith
    · linarith
  have hentries : ∀ n, |γ n 0 0| ≤ B ∧ |γ n 0 1| ≤ B ∧ |γ n 1 0| ≤ B ∧ |γ n 1 1| ≤ B := by
    intro n
    have hz' := hball_bounds _ _ (Metric.ball_subset_ball (min_le_right _ _) (hzs n))
    have hw' := hball_bounds _ _ (Metric.ball_subset_ball (min_le_right _ _) (hws n))
    exact hB (γ n) (hdetn n) ⟨zs n, hzsU n⟩ ⟨ws n, hwsU n⟩ (hγz n)
      ((min_le_left _ _).trans hz'.1) ((min_le_right _ _).trans hw'.1)
      (hz'.2.trans (le_max_left _ _)) (hw'.2.trans (le_max_right _ _))
  -- a convergent subsequence
  obtain ⟨L, -, φ, hφ, hlim⟩ :=
    ((isCompact_Icc (a := -B) (b := B)).prod ((isCompact_Icc (a := -B) (b := B)).prod
      ((isCompact_Icc (a := -B) (b := B)).prod (isCompact_Icc (a := -B) (b := B))))).tendsto_subseq
      (x := fun n => ((γ n 0 0, γ n 0 1, γ n 1 0, γ n 1 1) : ℝ × ℝ × ℝ × ℝ))
      (fun n => ⟨abs_le.mp (hentries n).1, abs_le.mp (hentries n).2.1,
        abs_le.mp (hentries n).2.2.1, abs_le.mp (hentries n).2.2.2⟩)
  have ha : Tendsto (fun n => γ (φ n) 0 0) atTop (𝓝 L.1) :=
    (continuous_fst.tendsto _).comp hlim
  have hb : Tendsto (fun n => γ (φ n) 0 1) atTop (𝓝 L.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hc' : Tendsto (fun n => γ (φ n) 1 0) atTop (𝓝 L.2.2.1) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have hd : Tendsto (fun n => γ (φ n) 1 1) atTop (𝓝 L.2.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have hdetL : L.1 * L.2.2.2 - L.2.1 * L.2.2.1 = 1 := by
    have h1 := (ha.mul hd).sub (hb.mul hc')
    have h2 : (fun n => γ (φ n) 0 0 * γ (φ n) 1 1 - γ (φ n) 0 1 * γ (φ n) 1 0) =
        fun _ => (1 : ℝ) := funext fun n => hdetn' (φ n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- convergence of the action
  have hact : ∀ (s : ℕ → ℂ) (s₀ : ℂ), 0 < s₀.im → Tendsto s atTop (𝓝 s₀) →
      Tendsto (fun n => ((γ (φ n) 0 0 : ℂ) * s n + γ (φ n) 0 1) /
        ((γ (φ n) 1 0 : ℂ) * s n + γ (φ n) 1 1)) atTop
        (𝓝 (((L.1 : ℂ) * s₀ + L.2.1) / ((L.2.2.1 : ℂ) * s₀ + L.2.2.2))) := by
    intro s s₀ hs₀ hs
    have hcast : ∀ {r : ℕ → ℝ} {r₀ : ℝ}, Tendsto r atTop (𝓝 r₀) →
        Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (r₀ : ℂ)) := fun hr =>
      (Complex.continuous_ofReal.tendsto _).comp hr
    have hnum := ((hcast ha).mul hs).add (hcast hb)
    have hden := ((hcast hc').mul hs).add (hcast hd)
    exact hnum.div hden (moebius_denom_ne_zero hdetL hs₀)
  -- the limit is a symmetry
  have hmem : glOfDetOne L.1 L.2.1 L.2.2.1 L.2.2.2 hdetL ∈ symmetryGroup (qSeriesFun (F.c k)) := by
    refine glOfDetOne_mem_symmetryGroup_of hdetL fun τ => ?_
    have h1 := hact (fun _ => (τ : ℂ)) τ τ.im_pos tendsto_const_nhds
    have hP : 0 < (((L.1 : ℂ) * τ + L.2.1) / ((L.2.2.1 : ℂ) * τ + L.2.2.2)).im := by
      rw [← coe_glOfDetOne_smul hdetL τ]
      exact UpperHalfPlane.im_pos _
    have hgc' : ContinuousAt g (((L.1 : ℂ) * τ + L.2.1) / ((L.2.2.1 : ℂ) * τ + L.2.2.2)) :=
      (hgA _ hP).continuousAt
    have h2 := hgc'.tendsto.comp h1
    have h3 : ∀ n, g (((γ (φ n) 0 0 : ℂ) * τ + γ (φ n) 0 1) /
        ((γ (φ n) 1 0 : ℂ) * τ + γ (φ n) 1 1)) = g τ := fun n => by
      rw [← hform, hg, qSeriesExt_coe, (hγG (φ n)).2 τ, qSeriesExt_coe]
    have h4 : (g ∘ fun n => ((γ (φ n) 0 0 : ℂ) * τ + γ (φ n) 0 1) /
        ((γ (φ n) 1 0 : ℂ) * τ + γ (φ n) 1 1)) = fun _ => g τ := funext h3
    rw [h4] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  refine ⟨_, hmem, UpperHalfPlane.ext ?_⟩
  rw [coe_glOfDetOne_smul]
  have h1 := hact (fun n => zs (φ n)) z z.im_pos (hzlim.comp hφ.tendsto_atTop)
  have h2 : ∀ n, ((γ (φ n) 0 0 : ℂ) * zs (φ n) + γ (φ n) 0 1) /
      ((γ (φ n) 1 0 : ℂ) * zs (φ n) + γ (φ n) 1 1) = ws (φ n) := fun n => by
    have := congrArg UpperHalfPlane.coe (hγz (φ n))
    rw [hform] at this
    exact this
  have h3 : Tendsto (fun n => ws (φ n)) atTop (𝓝 (w : ℂ)) := hwlim.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique h1 (h3.congr fun n => (h2 n).symm)

end VOA.Moonshine.ConwayNorton
