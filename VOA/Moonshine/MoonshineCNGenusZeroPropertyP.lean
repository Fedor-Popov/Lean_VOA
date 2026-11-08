/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroMoebius

/-!
# Genus zero on the abstract interface: equal values are related by the symmetry group

Property P (blueprint `Notes/moonshine/MOON_M8_LEAN.md`), away from doubly critical pairs. Let
`F` be a replicable family of period `N > 0` satisfying the prime Hecke identity and
`f = qSeriesFun (F.c k)`. If `f z = f w` and `f′` does not vanish at `w` (or at `z`), there is
`γ ∈ symmetryGroup f` with `γ • z = w`
(`exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero`,
`exists_mem_symmetryGroup_smul_eq_of_not_both_critical`).

Proof: the local symmetry `α = f⁻¹ ∘ f` at `z` (`exists_localSymmetry_of_deriv_ne_zero`) is not
locally constant, so `α′ ≠ 0` at some `z′` near `z`; on a small disc around `z′` it is a real
Möbius map `γ` of the symmetry group (`isMoebiusSymmetryOn_of_localSymmetry`); the identity
theorem on the disc of the local symmetry extends `α = γ` to `z`, so `γ z = α z = w`.

The doubly critical case `f′ z = f′ w = 0` (approximation by non-critical pairs and closedness of
`symmetryGroup f`) is not treated here.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-- The denominator of a real Möbius map of determinant one does not vanish on `ℍ`. -/
lemma moebius_denom_ne_zero {p q r s : ℝ} (h : p * s - q * r = 1) {u : ℂ} (hu : 0 < u.im) :
    (r : ℂ) * u + s ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero,
    Complex.zero_im] at him
  have hr : r = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 hu.ne'
  simp only [hr, Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_re,
    Complex.zero_re] at hre
  rw [hr, hre] at h
  simp at h

/-- **Equal values are related by the symmetry group** (property P, non-critical target). -/
theorem exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) (k : ℕ) (hB1 : PrimeHeckeIdentity F k) {z w : ℍ}
    (hzw : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w)
    (hd : _root_.deriv (qSeriesExt (F.c k)) (w : ℂ) ≠ 0) :
    ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ • z = w := by
  have hc := F.isJDominated k
  have hgd := differentiableOn_qSeriesExt hc
  have hz0 : 0 < (z : ℂ).im := z.im_pos
  obtain ⟨η₁, hη₁, α, hαz, hαd, hαU⟩ := exists_localSymmetry_of_deriv_ne_zero hgd hz0 w.im_pos
    (by rw [qSeriesExt_coe, qSeriesExt_coe]; exact hzw) hd
  -- a disc around `z` with closure in `ℍ`
  set η₂ := min η₁ ((z : ℂ).im / 2) with hη₂def
  have hη₂ : 0 < η₂ := lt_min hη₁ (half_pos hz0)
  have hB₂ : Metric.ball (z : ℂ) η₂ ⊆ Metric.ball (z : ℂ) η₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hB₂U : ∀ u ∈ Metric.ball (z : ℂ) η₂, 0 < u.im := fun u hu =>
    im_pos_of_mem_ball ((min_le_right _ _).trans (by linarith)) hu
  -- `α′` does not vanish identically
  have hex : ∃ z' ∈ Metric.ball (z : ℂ) η₂, _root_.deriv α z' ≠ 0 := by
    by_contra hcon
    have hzero : ∀ u ∈ Metric.ball (z : ℂ) η₂, _root_.deriv α u = 0 := fun u hu =>
      not_not.mp fun h => hcon ⟨u, hu, h⟩
    have hconst : ∀ u ∈ Metric.ball (z : ℂ) η₂, α u = α z := fun u hu =>
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
        (hαd.mono hB₂) (fun v hv => hzero v hv) hu (Metric.mem_ball_self hη₂)
    have hgconst : ∀ u ∈ Metric.ball (z : ℂ) η₂, qSeriesExt (F.c k) u = qSeriesExt (F.c k) w :=
      fun u hu => by rw [← (hαU u (hB₂ hu)).2, hconst u hu, hαz]
    have heq : EqOn (qSeriesExt (F.c k)) (fun _ => qSeriesExt (F.c k) w) upperHalfPlaneSet :=
      (hgd.analyticOnNhd isOpen_upperHalfPlaneSet).eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const (convex_halfSpace_im_gt 0).isPreconnected hz0
        (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hη₂) hgconst)
    obtain ⟨u, v, hu, hv, hne⟩ := qSeriesExt_exists_ne hc
    exact hne ((heq hu).trans (heq hv).symm)
  obtain ⟨z', hz'B, hdz'⟩ := hex
  -- a small disc around `z'` on which `Im α` is bounded below
  have hz'B₁ : z' ∈ Metric.ball (z : ℂ) η₁ := hB₂ hz'B
  have hαz'U : 0 < (α z').im := (hαU z' hz'B₁).1
  have hαc : ContinuousAt α z' :=
    (hαd.differentiableAt (Metric.isOpen_ball.mem_nhds hz'B₁)).continuousAt
  have hev : ∀ᶠ u in 𝓝 z', (α z').im / 2 ≤ (α u).im ∧ u ∈ Metric.ball (z : ℂ) η₂ :=
    (((Complex.continuous_im.tendsto _).comp hαc.tendsto).eventually
      (le_mem_nhds (half_lt_self hαz'U))).and (Metric.isOpen_ball.mem_nhds hz'B)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hz'0 : 0 < z'.im := hB₂U z' hz'B
  set ε := min ε₁ (z'.im / 2) with hεdef
  have hε : 0 < ε := lt_min hε₁ (half_pos hz'0)
  have hεz : ε < z'.im := (min_le_right _ _).trans_lt (half_lt_self hz'0)
  have hεB : Metric.ball z' ε ⊆ Metric.ball z' ε₁ := Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨p, q, r, s, hdet, hmem, hform⟩ := isMoebiusSymmetryOn_of_localSymmetry hN F k hB1 hε
    hεz (hαd.mono fun u hu => hB₂ (hball u (hεB hu)).2) (half_pos hαz'U)
    (fun u hu => (hball u (hεB hu)).1) (fun u hu => (hαU u (hB₂ (hball u (hεB hu)).2)).2) hdz'
  -- the identity theorem on the disc around `z`
  have hMd : DifferentiableOn ℂ (fun u : ℂ => ((p : ℂ) * u + q) / ((r : ℂ) * u + s))
      upperHalfPlaneSet := by
    have h1 : Differentiable ℂ fun u : ℂ => (p : ℂ) * u + q := by fun_prop
    have h2 : Differentiable ℂ fun u : ℂ => (r : ℂ) * u + s := by fun_prop
    exact h1.differentiableOn.div h2.differentiableOn fun u hu => moebius_denom_ne_zero hdet hu
  have hEq : ∀ u ∈ Metric.ball (z : ℂ) η₂, α u = ((p : ℂ) * u + q) / ((r : ℂ) * u + s) := by
    have hA1 : AnalyticOnNhd ℂ α (Metric.ball (z : ℂ) η₂) :=
      (hαd.mono hB₂).analyticOnNhd Metric.isOpen_ball
    have hA2 : AnalyticOnNhd ℂ (fun u : ℂ => ((p : ℂ) * u + q) / ((r : ℂ) * u + s))
        (Metric.ball (z : ℂ) η₂) :=
      (hMd.mono fun u hu => hB₂U u hu).analyticOnNhd Metric.isOpen_ball
    intro u hu
    exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_ball _ _).isPreconnected hz'B
      (Filter.eventually_of_mem (Metric.ball_mem_nhds z' (half_pos hε)) hform) hu
  refine ⟨glOfDetOne p q r s hdet, hmem, UpperHalfPlane.ext ?_⟩
  rw [coe_glOfDetOne_smul, ← hEq z (Metric.mem_ball_self hη₂), hαz]

/-- **Equal values are related by the symmetry group** (property P), whenever `f′` does not
vanish at both points. -/
theorem exists_mem_symmetryGroup_smul_eq_of_not_both_critical {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) (k : ℕ) (hB1 : PrimeHeckeIdentity F k) {z w : ℍ}
    (hzw : qSeriesFun (F.c k) z = qSeriesFun (F.c k) w)
    (hd : _root_.deriv (qSeriesExt (F.c k)) (z : ℂ) ≠ 0 ∨
      _root_.deriv (qSeriesExt (F.c k)) (w : ℂ) ≠ 0) :
    ∃ γ ∈ symmetryGroup (qSeriesFun (F.c k)), γ • z = w := by
  rcases hd with hdz | hdw
  · obtain ⟨γ, hγ, hγw⟩ :=
      exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero hN F k hB1 hzw.symm hdz
    refine ⟨γ⁻¹, (symmetryGroup _).inv_mem hγ, ?_⟩
    rw [← hγw, inv_smul_smul]
  · exact exists_mem_symmetryGroup_smul_eq_of_deriv_ne_zero hN F k hB1 hzw hdw

end VOA.Moonshine.ConwayNorton
