/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroAnalytic
import VOA.Moonshine.MoonshineCNGenusZeroInterface

/-!
# Genus zero on the abstract interface: large values come from the top

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. For a `J`-dominated `q`-series
`f = q⁻¹ + h(q)` and any height `Y₀`, every value `w` of large modulus is taken at a point of
height at least `Y₀` (`exists_large_values_from_height`); in particular
`LargeValuesFromTop f` (`largeValuesFromTop_qSeriesFun`).

Proof: `g(q) = q / (1 + q h(q))` is holomorphic near `0` with `g 0 = 0`, `g′ 0 = 1`, so by the
inverse function theorem (`HasStrictDerivAt.map_nhds_eq`) it maps a small disc onto a
neighbourhood of `0`; for `‖w‖` large, `w⁻¹ = g(q)` with `q ≠ 0` small, i.e. `q⁻¹ + h(q) = w`, and
`q = e^{2πiσ}` for a point `σ` high up (`Function.Periodic.invQParam`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology
open scoped Real MatrixGroups Manifold

local notation "𝕢" => Function.Periodic.qParam

/-- The regular part is holomorphic on the disc of radius `e^{−2π}`. -/
lemma qTailSeries_differentiableOn {c : ℕ → ℂ} (hc : IsJDominated c) :
    DifferentiableOn ℂ (qTailSeries c) (Metric.ball 0 (Real.exp (-2 * π * 1))) := by
  change DifferentiableOn ℂ (fun q : ℂ => ∑' n : ℕ, c (n + 1) * q ^ (n + 1)) _
  exact Complex.differentiableOn_tsum_of_summable_norm (F := fun n q => c (n + 1) * q ^ (n + 1))
    (summable_jCoeffMajorant_mul_exp one_pos)
    (fun n => ((differentiable_id.pow (n + 1)).const_mul (c (n + 1))).differentiableOn)
    Metric.isOpen_ball
    (fun n q hq => norm_qTail_term_le hc (le_of_lt (mem_ball_zero_iff.mp hq)) n)

/-- **Large values come from the top**, at any prescribed height. -/
theorem exists_large_values_from_height {c : ℕ → ℂ} (hc : IsJDominated c) (Y₀ : ℝ) :
    ∃ R : ℝ, ∀ w : ℂ, R ≤ ‖w‖ → ∃ σ : ℍ, Y₀ ≤ σ.im ∧ qSeriesFun c σ = w := by
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : 1 ≤ Y := le_max_right _ _
  set δ : ℝ := min (Real.exp (-2 * π * Y)) (1 / (jTail 1 + 1)) with hδdef
  have hJ0 := jTail_nonneg 1
  have hδ0 : 0 < δ := lt_min (Real.exp_pos _) (by positivity)
  have hδY : δ ≤ Real.exp (-2 * π * Y) := min_le_left _ _
  have hδ1 : δ ≤ Real.exp (-2 * π * 1) :=
    hδY.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos]))
  have hδJ : δ * jTail 1 < 1 := by
    have h1 : δ ≤ 1 / (jTail 1 + 1) := min_le_right _ _
    have h2 : δ * (jTail 1 + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- the auxiliary map `g q = q / (1 + q h(q))`
  set u : ℂ → ℂ := fun q => (1 + q * qTailSeries c q)⁻¹ with hudef
  set g : ℂ → ℂ := fun q => q * u q with hgdef
  have hden : ∀ q ∈ Metric.ball (0 : ℂ) δ, 1 + q * qTailSeries c q ≠ 0 := by
    intro q hq hzero
    have hq' : ‖q‖ < δ := mem_ball_zero_iff.mp hq
    have hh : ‖qTailSeries c q‖ ≤ jTail 1 := norm_qTailSeries_le hc one_pos (hq'.le.trans hδ1)
    have h1 : q * qTailSeries c q = -1 := by linear_combination hzero
    have h2 : ‖q * qTailSeries c q‖ = 1 := by rw [h1, norm_neg, norm_one]
    rw [norm_mul] at h2
    nlinarith [norm_nonneg q, norm_nonneg (qTailSeries c q)]
  have hball : Metric.ball (0 : ℂ) δ ⊆ Metric.ball 0 (Real.exp (-2 * π * 1)) :=
    Metric.ball_subset_ball hδ1
  have hhol := (qTailSeries_differentiableOn hc).mono hball
  have hud : DifferentiableOn ℂ u (Metric.ball 0 δ) :=
    ((differentiableOn_const 1).add (differentiableOn_id.mul hhol)).inv hden
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 δ) := differentiableOn_id.mul hud
  have hnhds : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hδ0
  have hu0 : u 0 = 1 := by simp [hudef]
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hgder : HasDerivAt g 1 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).mul ((hud.differentiableAt hnhds).hasDerivAt)
    simpa [hu0] using h
  have hstrict : HasStrictDerivAt g 1 0 := by
    have h := (hgd.analyticAt hnhds).hasStrictDerivAt
    rwa [hgder.deriv] at h
  have hmap := HasStrictDerivAt.map_nhds_eq hstrict one_ne_zero
  have himg : g '' Metric.ball 0 δ ∈ 𝓝 (0 : ℂ) := by
    have h : g '' Metric.ball 0 δ ∈ map g (𝓝 (0 : ℂ)) := Filter.image_mem_map hnhds
    rwa [hmap, hg0] at h
  obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨2 / ε, fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact absurd hw (not_le.mpr (by positivity))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwinv : w⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_inv]
    have h1 : 2 ≤ ε * ‖w‖ := by rwa [div_le_iff₀ hε0, mul_comm] at hw
    rw [inv_lt_comm₀ hwpos hε0]
    have : 1 / ε < ‖w‖ := by
      rw [div_lt_iff₀ hε0]
      linarith
    simpa using this
  obtain ⟨q, hqδ, hgq⟩ := hεsub hwinv
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hg0] at hgq
    exact inv_ne_zero hw0 hgq.symm
  have hq' : ‖q‖ < δ := mem_ball_zero_iff.mp hqδ
  have hdq := hden q hqδ
  have hval : q⁻¹ + qTailSeries c q = w := by
    have h1 : q * (1 + q * qTailSeries c q)⁻¹ = w⁻¹ := hgq
    field_simp at h1
    field_simp
    linear_combination -h1
  have him : 0 < (Function.Periodic.invQParam 1 q).im := by
    rw [Function.Periodic.im_invQParam]
    have hlog : Real.log ‖q‖ < 0 :=
      Real.log_neg (norm_pos_iff.mpr hq0) (hq'.trans_le (hδY.trans
        (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))) |>.trans_le le_rfl)
    have : 0 < -1 / (2 * π) * Real.log ‖q‖ := by
      have h2 : -1 / (2 * π) < 0 := by
        apply div_neg_of_neg_of_pos (by norm_num) (by positivity)
      nlinarith
    exact this
  refine ⟨⟨Function.Periodic.invQParam 1 q, him⟩, ?_, ?_⟩
  · change Y₀ ≤ (Function.Periodic.invQParam 1 q).im
    rw [Function.Periodic.im_invQParam]
    have hlog : Real.log ‖q‖ ≤ -2 * π * Y := by
      rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr hq0)]
      exact hq'.le.trans hδY
    have hY0 : Y₀ ≤ Y := le_max_left _ _
    have hpi : 0 < 2 * π := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith
  · have hqp : qPar ⟨Function.Periodic.invQParam 1 q, him⟩ = q :=
      Function.Periodic.qParam_right_inv one_ne_zero hq0
    rw [qSeriesFun_eq_inv_add_qTailSeries, hqp, hval]

/-- `LargeValuesFromTop` for every `J`-dominated `q`-series (height `1`). -/
theorem largeValuesFromTop_qSeriesFun {c : ℕ → ℂ} (hc : IsJDominated c) :
    LargeValuesFromTop (qSeriesFun c) := by
  obtain ⟨R, hR⟩ := exists_large_values_from_height hc 1
  exact ⟨R, 1, one_pos, hR⟩

/-- Every member of a replicable family takes its large values high up. -/
theorem ReplicableFamily.largeValuesFromTop {N : ℕ} (F : ReplicableFamily N) (k : ℕ) :
    LargeValuesFromTop (qSeriesFun (F.c k)) :=
  largeValuesFromTop_qSeriesFun (F.isJDominated k)

end VOA.Moonshine.ConwayNorton
