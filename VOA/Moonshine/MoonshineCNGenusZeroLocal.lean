/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroPartner
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Genus zero on the abstract interface: local symmetries near a non-critical value, and the top

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`.

* `exists_localSymmetry_of_deriv_ne_zero` (local symmetry at a non-critical value): if `g` is
  holomorphic on the upper half-plane, `g z₀ = g w₀` and `g′ w₀ ≠ 0`, there is a holomorphic
  `α` on a disc around `z₀` with `α z₀ = w₀`, values in the upper half-plane and `g ∘ α = g`
  (namely `α = g⁻¹ ∘ g` with the analytic local inverse of `g` at `w₀`).
* `eq_of_continuousOn_intValued`: a continuous integer-valued real function on a preconnected set
  is constant (intermediate value theorem).
* `exists_int_eq_add_of_top` (relations in the top are integer translations): if
  `f ∘ u = f ∘ v` on a preconnected set and `u`, `v` take values above `topHeight`, then
  `u = v + n` for one integer `n`.
* `exists_affC_eqOn_of_top` (the same, in the form used by the overlap construction): if
  `f (δ z + τ) = f (μ α z + ν)` on a connected open `D`, the right side lies above `topHeight`
  everywhere and the left side somewhere, then `α` is a real affine map `z ↦ a z + b`, `a > 0`,
  on all of `D`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### A local symmetry at a non-critical target -/

/-- **Local symmetry at a non-critical value**. -/
theorem exists_localSymmetry_of_deriv_ne_zero {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g upperHalfPlaneSet) {z₀ w₀ : ℂ} (hz₀ : 0 < z₀.im)
    (hw₀ : 0 < w₀.im) (heq : g z₀ = g w₀) (hd : _root_.deriv g w₀ ≠ 0) :
    ∃ η > 0, ∃ α : ℂ → ℂ, α z₀ = w₀ ∧ DifferentiableOn ℂ α (Metric.ball z₀ η) ∧
      ∀ z ∈ Metric.ball z₀ η, 0 < (α z).im ∧ g (α z) = g z := by
  have hgA := hg.analyticOnNhd isOpen_upperHalfPlaneSet
  have hgw : AnalyticAt ℂ g w₀ := hgA w₀ hw₀
  have hgz : AnalyticAt ℂ g z₀ := hgA z₀ hz₀
  set φ := hgw.hasStrictDerivAt.localInverse _ _ _ hd with hφdef
  have hφ : AnalyticAt ℂ φ (g w₀) := hgw.analyticAt_localInverse hd
  have hφw : φ (g w₀) = w₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hright : ∀ᶠ y in 𝓝 (g w₀), g (φ y) = y :=
    hgw.hasStrictDerivAt.eventually_right_inverse hd
  have hφz : AnalyticAt ℂ φ (g z₀) := by rw [heq]; exact hφ
  have hα : AnalyticAt ℂ (φ ∘ g) z₀ := hφz.comp hgz
  have hαz₀ : (φ ∘ g) z₀ = w₀ := by simp only [Function.comp_apply, heq, hφw]
  have h1 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ (φ ∘ g) z := hα.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 z₀, g (φ (g z)) = g z := by
    have ht : Tendsto g (𝓝 z₀) (𝓝 (g w₀)) := by
      rw [← heq]
      exact hgz.continuousAt.tendsto
    exact ht.eventually hright
  have h3 : ∀ᶠ z in 𝓝 z₀, 0 < ((φ ∘ g) z).im := by
    have hU : upperHalfPlaneSet ∈ 𝓝 ((φ ∘ g) z₀) := by
      rw [hαz₀]
      exact isOpen_upperHalfPlaneSet.mem_nhds hw₀
    exact hα.continuousAt.preimage_mem_nhds hU
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
  refine ⟨η, hη, φ ∘ g, hαz₀, fun z hz => (hball z hz).1.differentiableAt.differentiableWithinAt,
    fun z hz => ⟨(hball z hz).2.2, (hball z hz).2.1⟩⟩

/-! ### Integer-valued continuous functions -/

lemma not_lt_of_intValued_aux {S : Set ℂ} (hS : IsPreconnected S) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ S) (hint : ∀ z ∈ S, ∃ m : ℤ, φ z = m) {z w : ℂ} (hz : z ∈ S)
    (hw : w ∈ S) : ¬ φ z < φ w := by
  intro hlt
  obtain ⟨a, ha⟩ := hint z hz
  obtain ⟨b, hb⟩ := hint w hw
  rw [ha, hb] at hlt
  have hab : a < b := by exact_mod_cast hlt
  have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hmem : (a : ℝ) + 1 / 2 ∈ Icc (φ z) (φ w) := by
    rw [ha, hb]
    constructor <;> linarith
  obtain ⟨x, hx, hxeq⟩ := hS.intermediate_value hz hw hφ hmem
  obtain ⟨m, hm⟩ := hint x hx
  rw [hm] at hxeq
  rcases le_or_gt m a with h | h
  · have : (m : ℝ) ≤ a := by exact_mod_cast h
    linarith
  · have h' : a + 1 ≤ m := h
    have : (a : ℝ) + 1 ≤ m := by exact_mod_cast h'
    linarith

/-- A continuous integer-valued real function on a preconnected set is constant. -/
lemma eq_of_continuousOn_intValued {S : Set ℂ} (hS : IsPreconnected S) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ S) (hint : ∀ z ∈ S, ∃ m : ℤ, φ z = m) {z w : ℂ} (hz : z ∈ S)
    (hw : w ∈ S) : φ z = φ w :=
  le_antisymm (not_lt.mp (not_lt_of_intValued_aux hS hφ hint hw hz))
    (not_lt.mp (not_lt_of_intValued_aux hS hφ hint hz hw))

/-! ### Relations in the top are integer translations -/

/-- **Relations in the top are integer translations**. If `f ∘ u = f ∘ v` on a preconnected
set `S`, with `u`, `v` continuous and taking values above `topHeight`, then `u = v + n` on `S`
for a single integer `n`. -/
theorem exists_int_eq_add_of_top {c : ℕ → ℂ} (hc : IsJDominated c) {S : Set ℂ}
    (hS : IsPreconnected S) {u v : ℂ → ℂ} (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (htu : ∀ z ∈ S, topHeight ≤ (u z).im) (htv : ∀ z ∈ S, topHeight ≤ (v z).im)
    (huv : ∀ z ∈ S, qSeriesExt c (u z) = qSeriesExt c (v z)) :
    ∃ n : ℤ, ∀ z ∈ S, u z = v z + n := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₁, hz₁⟩
  · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
  have hint : ∀ z ∈ S, ∃ n : ℤ, u z = v z + n := fun z hz =>
    exists_int_of_qSeriesExt_eq hc (htu z hz) (htv z hz) (huv z hz)
  obtain ⟨n₁, hn₁⟩ := hint z₁ hz₁
  refine ⟨n₁, fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := hint z hz
  set φ : ℂ → ℝ := fun z => (u z - v z).re with hφdef
  have hφc : ContinuousOn φ S := Complex.continuous_re.comp_continuousOn (hu.sub hv)
  have hφint : ∀ z ∈ S, ∃ m : ℤ, φ z = m := fun z hz => by
    obtain ⟨m, hm⟩ := hint z hz
    exact ⟨m, by simp [φ, hm]⟩
  have hφz : φ z = n := by simp [φ, hn]
  have hφz₁ : φ z₁ = n₁ := by simp [φ, hn₁]
  have heq := eq_of_continuousOn_intValued hS hφc hφint hz hz₁
  rw [hφz, hφz₁] at heq
  have hnn : n = n₁ := by exact_mod_cast heq
  rw [hn, hnn]

/-- **A relation reaching the top is real affine** (overlap form). Let `D` be a connected open
set, `α` holomorphic on `D`, and `f (δ z + τ) = f (μ α(z) + ν)` on `D` with `δ, μ > 0`. If
`μ α(z) + ν` lies above `topHeight` for every `z ∈ D` and `δ z₁ + τ` lies strictly above it for one
`z₁ ∈ D`, then `α` is a real affine map `z ↦ a z + b` with `a > 0` on all of `D`. -/
theorem exists_affC_eqOn_of_top {c : ℕ → ℂ} (hc : IsJDominated c) {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) {α : ℂ → ℂ} (hα : DifferentiableOn ℂ α D) {δ τ μ ν : ℝ}
    (hδ : 0 < δ) (hμ : 0 < μ)
    (hrel : ∀ z ∈ D, qSeriesExt c (affC δ τ z) = qSeriesExt c (affC μ ν (α z)))
    (htop : ∀ z ∈ D, topHeight ≤ (affC μ ν (α z)).im) {z₁ : ℂ} (hz₁ : z₁ ∈ D)
    (hz₁top : topHeight < (affC δ τ z₁).im) :
    ∃ a b : ℝ, 0 < a ∧ ∀ z ∈ D, α z = affC a b z := by
  set W : Set ℂ := D ∩ {z | topHeight < (affC δ τ z).im} with hWdef
  have hWo : IsOpen W :=
    hDo.inter (isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_affC δ τ)))
  obtain ⟨ε, hε, hballW⟩ := Metric.isOpen_iff.mp hWo z₁ ⟨hz₁, hz₁top⟩
  have hballD : Metric.ball z₁ ε ⊆ D := fun z hz => (hballW hz).1
  obtain ⟨n, hn⟩ := exists_int_eq_add_of_top hc (convex_ball z₁ ε).isPreconnected
    (u := fun z => affC μ ν (α z)) (v := affC δ τ)
    ((continuous_affC μ ν).comp_continuousOn (hα.continuousOn.mono hballD))
    (continuous_affC δ τ).continuousOn (fun z hz => htop z (hballD hz))
    (fun z hz => (hballW hz).2.le) (fun z hz => (hrel z (hballD hz)).symm)
  have hμ' : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  refine ⟨δ / μ, (τ + n - ν) / μ, div_pos hδ hμ, ?_⟩
  have hball_eq : ∀ z ∈ Metric.ball z₁ ε, α z = affC (δ / μ) ((τ + n - ν) / μ) z := by
    intro z hz
    have h1 := hn z hz
    simp only [affC] at h1
    have h2 : (μ : ℂ) * α z = δ * z + τ + n - ν := by linear_combination h1
    rw [← inv_mul_cancel_left₀ hμ' (α z), h2]
    simp only [affC]
    push_cast
    ring
  have hαA : AnalyticOnNhd ℂ α D := hα.analyticOnNhd hDo
  have hLA : AnalyticOnNhd ℂ (affC (δ / μ) ((τ + n - ν) / μ)) D :=
    (differentiable_affC _ _).differentiableOn.analyticOnNhd hDo
  have hev : α =ᶠ[𝓝 z₁] affC (δ / μ) ((τ + n - ν) / μ) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds z₁ hε) hball_eq
  exact fun z hz => hαA.eqOn_of_preconnected_of_eventuallyEq hLA hDc hz₁ hev hz

end VOA.Moonshine.ConwayNorton
