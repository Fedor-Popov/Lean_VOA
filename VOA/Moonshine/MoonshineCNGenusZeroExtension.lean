/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroBoundary
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Genus zero on the abstract interface: global extension of a local symmetry

First half of "local symmetries are real Möbius maps" (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`). Let `β` be holomorphic on the whole upper half-plane with
nowhere-vanishing derivative (the explicit solutions of the real linear ODE are of this kind),
and let `f ∘ β = f` near one point `z₀` with `β z₀ ∈ ℍ`. Then `β` maps `ℍ` into `ℍ` and
`f ∘ β = f` on all of `ℍ` (`forall_im_pos_and_eq_of_local`).

Proof. Let `W` be the connected component through `z₀` of `{z ∈ ℍ | β z ∈ ℍ}`; `f ∘ β = f` on `W`
by the identity theorem. `W` is relatively closed in `ℍ`: at a point `z₁ ∈ ℍ ∩ closure W` either
`β z₁ ∈ ℍ` (then a disc around `z₁` lies in `W`) or `β z₁ = x₁ ∈ ℝ`. In the latter case the analytic
local inverse `v` of `β` at `z₁` is an injective holomorphic map of a half-disc
`D(x₁, r) ∩ ℍ` into a closed disc `D̄(z₁, ρ) ⊆ ℍ`, its image is a connected subset of
`{β ∈ ℍ}` meeting `W`, hence lies in `W`, so `f ∘ v = f` on the half-disc, which the
boundary-real exclusion (`false_of_halfDisc_symmetry`) forbids. As `ℍ` is connected, `W = ℍ`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-- **Global extension of a local symmetry**. -/
theorem forall_im_pos_and_eq_of_local {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N) (k : ℕ)
    (hB1 : PrimeHeckeIdentity F k) {β : ℂ → ℂ} (hβ : DifferentiableOn ℂ β upperHalfPlaneSet)
    (hβ' : ∀ z : ℂ, 0 < z.im → _root_.deriv β z ≠ 0) {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    (hβz₀ : 0 < (β z₀).im)
    (hloc : ∀ᶠ z in 𝓝 z₀, qSeriesExt (F.c k) (β z) = qSeriesExt (F.c k) z) :
    ∀ z : ℂ, 0 < z.im → 0 < (β z).im ∧ qSeriesExt (F.c k) (β z) = qSeriesExt (F.c k) z := by
  have hc := F.isJDominated k
  set U : Set ℂ := upperHalfPlaneSet with hU
  set O : Set ℂ := U ∩ β ⁻¹' U with hO
  have hOo : IsOpen O :=
    hβ.continuousOn.isOpen_inter_preimage isOpen_upperHalfPlaneSet isOpen_upperHalfPlaneSet
  have hz₀O : z₀ ∈ O := ⟨hz₀, hβz₀⟩
  set W : Set ℂ := connectedComponentIn O z₀ with hW
  have hWo : IsOpen W := hOo.connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWO : W ⊆ O := connectedComponentIn_subset O z₀
  have hz₀W : z₀ ∈ W := mem_connectedComponentIn hz₀O
  -- the relation on `W`
  have hrelW : ∀ z ∈ W, qSeriesExt (F.c k) (β z) = qSeriesExt (F.c k) z := by
    have hA1 : AnalyticOnNhd ℂ (qSeriesExt (F.c k) ∘ β) W :=
      ((differentiableOn_qSeriesExt hc).comp (hβ.mono fun z hz => (hWO hz).1)
        fun z hz => (hWO hz).2).analyticOnNhd hWo
    have hA2 : AnalyticOnNhd ℂ (qSeriesExt (F.c k)) W :=
      ((differentiableOn_qSeriesExt hc).mono fun z hz => (hWO hz).1).analyticOnNhd hWo
    intro z hz
    exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hWc hz₀W hloc hz
  -- `W` is relatively closed in `ℍ`
  have hclosed : closure W ∩ U ⊆ W := by
    rintro z₁ ⟨hz₁W, hz₁U⟩
    have hz₁U' : 0 < z₁.im := hz₁U
    have hβA : AnalyticAt ℂ β z₁ := hβ.analyticOnNhd isOpen_upperHalfPlaneSet z₁ hz₁U
    have hβc : ContinuousAt β z₁ := hβA.continuousAt
    have hfreqW : ∃ᶠ z in 𝓝 z₁, z ∈ W := mem_closure_iff_frequently.mp hz₁W
    have hge : 0 ≤ (β z₁).im := by
      by_contra hlt
      have hlt' := lt_of_not_ge hlt
      have hev : ∀ᶠ z in 𝓝 z₁, (β z).im < 0 :=
        ((Complex.continuous_im.tendsto _).comp hβc.tendsto).eventually (gt_mem_nhds hlt')
      obtain ⟨z, hzW, hz⟩ := (hfreqW.and_eventually hev).exists
      exact absurd (hWO hzW).2 (not_lt.mpr hz.le)
    rcases hge.lt_or_eq with hpos | hzero
    · -- an interior point: a disc around `z₁` lies in `W`
      have hz₁O : z₁ ∈ O := ⟨hz₁U, hpos⟩
      obtain ⟨ε, hε, hballO⟩ := Metric.isOpen_iff.mp hOo z₁ hz₁O
      obtain ⟨x, hxW, hxball⟩ := (hfreqW.and_eventually (Metric.ball_mem_nhds z₁ hε)).exists
      have hsub : Metric.ball z₁ ε ⊆ connectedComponentIn O x :=
        (convex_ball z₁ ε).isPreconnected.subset_connectedComponentIn hxball hballO
      rw [← connectedComponentIn_eq hxW] at hsub
      exact hsub (Metric.mem_ball_self hε)
    · -- a boundary-real point: excluded by the boundary-real exclusion
      exfalso
      set x₁ : ℝ := (β z₁).re with hx₁
      have hβz₁ : β z₁ = (x₁ : ℂ) := Complex.ext (by simp [hx₁]) (by simp [← hzero])
      have hd := hβ' z₁ hz₁U
      set φ := hβA.hasStrictDerivAt.localInverse _ _ _ hd with hφdef
      have hφA : AnalyticAt ℂ φ (β z₁) := hβA.analyticAt_localInverse hd
      have hφz : φ (β z₁) = z₁ := HasStrictFDerivAt.localInverse_apply_image ..
      have hright : ∀ᶠ y in 𝓝 (β z₁), β (φ y) = y :=
        hβA.hasStrictDerivAt.eventually_right_inverse hd
      have hleft : ∀ᶠ z in 𝓝 z₁, φ (β z) = z :=
        hβA.hasStrictDerivAt.eventually_left_inverse hd
      set ρ : ℝ := z₁.im / 2 with hρ
      have hρ0 : 0 < ρ := half_pos hz₁U'
      have hρz : ρ < z₁.im := half_lt_self hz₁U'
      have hφball : ∀ᶠ y in 𝓝 (β z₁), φ y ∈ Metric.ball z₁ ρ := by
        have h := hφA.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ0)
        rw [hφz] at h
        exact h
      obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff_ball.mp
        (hφA.eventually_analyticAt.and (hright.and hφball))
      rw [hβz₁] at hrball
      set H : Set ℂ := Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet with hH
      have hvd : DifferentiableOn ℂ φ H := fun w hw =>
        (hrball w hw.1).1.differentiableAt.differentiableWithinAt
      have hinj : InjOn φ H := by
        intro a ha b hb hab
        rw [← (hrball a ha.1).2.1, ← (hrball b hb.1).2.1, hab]
      have hvK : ∀ w ∈ H, φ w ∈ Metric.closedBall z₁ ρ := fun w hw =>
        Metric.ball_subset_closedBall (hrball w hw.1).2.2
      have hφim : ∀ w ∈ H, 0 < (φ w).im := by
        intro w hw
        have h1 := (hrball w hw.1).2.2
        rw [Metric.mem_ball, dist_eq_norm] at h1
        have h2 := Complex.abs_im_le_norm (φ w - z₁)
        rw [Complex.sub_im] at h2
        have h3 := (abs_lt.mp (h2.trans_lt h1)).1
        linarith
      -- the image of the half-disc lies in `W`
      have hHc : IsPreconnected H :=
        ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
      have himgO : φ '' H ⊆ O := by
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨hφim w hw, ?_⟩
        change 0 < (β (φ w)).im
        rw [(hrball w hw.1).2.1]
        exact hw.2
      have hmeet : ∃ z ∈ W, z ∈ φ '' H := by
        have hβt : ∀ᶠ z in 𝓝 z₁, β z ∈ Metric.ball (x₁ : ℂ) r := by
          have h := hβc.preimage_mem_nhds (Metric.ball_mem_nhds (β z₁) hr)
          rw [hβz₁] at h
          exact h
        obtain ⟨z, hzW, hzl, hzt⟩ := (hfreqW.and_eventually (hleft.and hβt)).exists
        exact ⟨z, hzW, β z, ⟨hzt, (hWO hzW).2⟩, hzl⟩
      obtain ⟨z, hzW, hzimg⟩ := hmeet
      have himgW : φ '' H ⊆ W := by
        have h := (hHc.image φ hvd.continuousOn).subset_connectedComponentIn hzimg himgO
        rwa [← connectedComponentIn_eq hzW] at h
      have hvf : ∀ w ∈ H, qSeriesExt (F.c k) (φ w) = qSeriesExt (F.c k) w := by
        intro w hw
        have h1 := hrelW (φ w) (himgW ⟨w, hw, rfl⟩)
        rw [(hrball w hw.1).2.1] at h1
        exact h1.symm
      exact false_of_halfDisc_symmetry hN F k hB1 hr hvd hinj hρz hvK hvf
  -- `W = ℍ`
  have hUW : U ⊆ W :=
    (convex_halfSpace_im_gt 0).isPreconnected.subset_of_closure_inter_subset hWo
      ⟨z₀, hz₀, hz₀W⟩ hclosed
  intro z hz
  exact ⟨(hWO (hUW hz)).2, hrelW z (hUW hz)⟩

end VOA.Moonshine.ConwayNorton
