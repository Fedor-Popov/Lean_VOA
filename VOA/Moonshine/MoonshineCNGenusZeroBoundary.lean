/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroLocal
import VOA.Moonshine.MoonshineCNGenusZeroShimizu
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Genus zero on the abstract interface: the boundary-real exclusion

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`; this is the local form of Cummins–Gannon's
Prop. 4.6. No local symmetry of a replicable member `f` maps a half-disc at a
real point into a compact subset of `ℍ`:

`false_of_halfDisc_symmetry`: there is no injective holomorphic `v` on
`H = D(x₁, r) ∩ ℍ` (`x₁ ∈ ℝ`) with values in a closed disc `D̄(z₁, ρ) ⊆ ℍ` and `f ∘ v = f` on `H`.

Proof. Transport by a large admissible prime `p` (pairing on connected domains) with the
scaling `w ↦ p w` on the half-disc side: `f (p w) = f (β (v w))` on `H` for one `β ∈ Δ(p)`.

* `β = (p 0; 0 1)`: `f (p w) = f (p v(w))`, with `p v(w)` in the top everywhere and `p w` in the
  top somewhere, so `v` is real affine (`exists_affC_eqOn_of_top`); a real affine map sends
  points of `H` close to `x₁` close to `ℝ`, against `Im v ≥ Im z₁ − ρ > 0`.
* `β = (1 j; 0 p)`: after an integer translation, `τ(w) = ((v w + j)/p + m)/p` is an injective
  self-map of `H` into a closed disc `K ⊆ H` of radius `ρ/p²` near `x₁`, with `G ∘ τ = G` for
  `G(z) = f(p z)`. The iterates of a point of `H \ K` are pairwise distinct and accumulate in
  `K ⊆ ℍ`, so `G` is constant (`eq_of_comp_eq_of_mapsTo_compact`); then `f` is constant, which
  it is not (`qSeriesFun_exists_ne`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Constancy from a contracting self-map -/

/-- **Iterates of an injective self-map into a compact set force constancy.** Let `G` be
holomorphic on a connected open set `U ⊇ H`, `τ` injective on `H` with `τ(H) ⊆ K`, `K ⊆ H`
compact, and `G ∘ τ = G` on `H`. If some `w₀ ∈ H` lies outside `K`, then `G` is constant on `U`. -/
theorem eq_of_comp_eq_of_mapsTo_compact {G : ℂ → ℂ} {U H K : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hG : DifferentiableOn ℂ G U) (hHU : H ⊆ U) (hKc : IsCompact K)
    (hKH : K ⊆ H) {τ : ℂ → ℂ} (hτK : ∀ w ∈ H, τ w ∈ K) (hτinj : InjOn τ H)
    (hGτ : ∀ w ∈ H, G (τ w) = G w) {w₀ : ℂ} (hw₀ : w₀ ∈ H) (hw₀K : w₀ ∉ K) :
    ∀ z ∈ U, G z = G w₀ := by
  have hsH : ∀ n : ℕ, τ^[n] w₀ ∈ H := by
    intro n
    induction n with
    | zero => exact hw₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hKH (hτK _ ih)
  have hsK : ∀ n : ℕ, τ^[n + 1] w₀ ∈ K := fun n => by
    rw [Function.iterate_succ_apply']
    exact hτK _ (hsH n)
  have hsG : ∀ n : ℕ, G (τ^[n] w₀) = G w₀ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', hGτ _ (hsH n), ih]
  have hinj : ∀ a b : ℕ, τ^[a] w₀ = τ^[b] w₀ → a = b := by
    intro a
    induction a with
    | zero =>
      intro b h
      cases b with
      | zero => rfl
      | succ b =>
        exfalso
        rw [Function.iterate_zero_apply] at h
        exact hw₀K (h ▸ hsK b)
    | succ a ih =>
      intro b h
      cases b with
      | zero =>
        exfalso
        rw [Function.iterate_zero_apply] at h
        exact hw₀K (h ▸ hsK a)
      | succ b =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
        rw [ih b (hτinj (hsH a) (hsH b) h)]
  obtain ⟨w', hw'K, φ, hφ, hlim⟩ := hKc.tendsto_subseq (x := fun n => τ^[n + 1] w₀) hsK
  have hev : ∀ᶠ n in atTop, τ^[φ n + 1] w₀ ≠ w' := by
    by_cases h : ∃ n₁, τ^[φ n₁ + 1] w₀ = w'
    · obtain ⟨n₁, hn₁⟩ := h
      refine eventually_atTop.mpr ⟨n₁ + 1, fun n hn heq => ?_⟩
      have h1 : φ n + 1 = φ n₁ + 1 := hinj _ _ (heq.trans hn₁.symm)
      have h2 : n = n₁ := hφ.injective (by omega)
      omega
    · exact Eventually.of_forall (not_exists.mp h)
  have htend : Tendsto (fun n => τ^[φ n + 1] w₀) atTop (𝓝[≠] w') :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hev.mono fun n hn => hn⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] w', G z = G w₀ :=
    htend.frequently (Frequently.of_forall fun n => hsG (φ n + 1))
  intro z hz
  exact (hG.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hUc
    (hHU (hKH hw'K)) hfreq hz

/-! ### Elementary estimates -/

lemma norm_affC_sub_affC (a b : ℝ) (z w : ℂ) : ‖affC a b z - affC a b w‖ = |a| * ‖z - w‖ := by
  have h : affC a b z - affC a b w = (a : ℂ) * (z - w) := by
    simp only [affC]
    ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma injOn_affC_comp {a b : ℝ} (ha : a ≠ 0) {v : ℂ → ℂ} {H : Set ℂ} (hv : InjOn v H) :
    InjOn (fun w => affC a b (v w)) H := by
  intro z hz w hw h
  apply hv hz hw
  have := congrArg (affC a⁻¹ (-(b / a))) h
  simpa only [affC_inv_affC ha] using this

/-- A `J`-dominated `q`-series read on `ℂ` is not constant on the upper half-plane. -/
lemma qSeriesExt_exists_ne {c : ℕ → ℂ} (hc : IsJDominated c) :
    ∃ z w : ℂ, 0 < z.im ∧ 0 < w.im ∧ qSeriesExt c z ≠ qSeriesExt c w := by
  obtain ⟨τ, σ, h⟩ := qSeriesFun_exists_ne hc
  exact ⟨τ, σ, τ.im_pos, σ.im_pos, by rwa [qSeriesExt_coe, qSeriesExt_coe]⟩

/-! ### The boundary-real exclusion -/

/-- **Boundary-real exclusion**. For a replicable family of period `N > 0` satisfying the
prime Hecke identity, there is no injective holomorphic map `v` from a half-disc
`H = D(x₁, r) ∩ ℍ` at a real point `x₁` into a closed disc `D̄(z₁, ρ)` with `ρ < Im z₁` such
that `f ∘ v = f` on `H`, where `f = qSeriesFun (F.c k)`. -/
theorem false_of_halfDisc_symmetry {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N) (k : ℕ)
    (hB1 : PrimeHeckeIdentity F k) {x₁ r : ℝ} (hr : 0 < r) {v : ℂ → ℂ}
    (hv : DifferentiableOn ℂ v (Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet))
    (hinj : InjOn v (Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet)) {z₁ : ℂ} {ρ : ℝ}
    (hρz : ρ < z₁.im)
    (hvK : ∀ w ∈ Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet, v w ∈ Metric.closedBall z₁ ρ)
    (hvf : ∀ w ∈ Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet,
      qSeriesExt (F.c k) (v w) = qSeriesExt (F.c k) w) : False := by
  have hc := F.isJDominated k
  set H : Set ℂ := Metric.ball (x₁ : ℂ) r ∩ upperHalfPlaneSet with hHdef
  have hHo : IsOpen H := Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet
  have hHc : IsPreconnected H :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  -- the test point `w₀ = x₁ + i r/2`
  set w₀ : ℂ := (x₁ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I with hw₀def
  have hw₀re : w₀.re = x₁ := by simp [hw₀def]
  have hw₀im : w₀.im = r / 2 := by simp [hw₀def]
  have hw₀dist : ‖w₀ - x₁‖ = r / 2 := by
    rw [hw₀def, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have hw₀ : w₀ ∈ H := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, hw₀dist]
      linarith
    · change 0 < w₀.im
      rw [hw₀im]
      exact half_pos hr
  have hρ0 : 0 ≤ ρ := Metric.nonempty_closedBall.mp ⟨_, hvK w₀ hw₀⟩
  set y₀ : ℝ := z₁.im - ρ with hy₀def
  have hy₀ : 0 < y₀ := by rw [hy₀def]; linarith
  have hvim : ∀ w ∈ H, y₀ ≤ (v w).im := by
    intro w hw
    have h1 := hvK w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at h1
    have h2 := Complex.abs_im_le_norm (v w - z₁)
    rw [Complex.sub_im] at h2
    have h3 := (abs_le.mp (h2.trans h1)).1
    rw [hy₀def]
    linarith
  have hvU : ∀ w ∈ H, 0 < (v w).im := fun w hw => hy₀.trans_le (hvim w hw)
  -- a large admissible prime
  set P₀ : ℝ := 2 * topHeight / r + topHeight / y₀ + 2 * (1 + z₁.im + ρ) / r with hP₀
  have hz₁im : 0 < z₁.im := by linarith
  have ht0 := topHeight_pos
  have hP₀1 : 2 * topHeight / r ≤ P₀ := by
    have : 0 ≤ topHeight / y₀ := div_nonneg ht0.le hy₀.le
    have : 0 ≤ 2 * (1 + z₁.im + ρ) / r := div_nonneg (by linarith) hr.le
    linarith
  have hP₀2 : topHeight / y₀ ≤ P₀ := by
    have : 0 ≤ 2 * topHeight / r := div_nonneg (by linarith) hr.le
    have : 0 ≤ 2 * (1 + z₁.im + ρ) / r := div_nonneg (by linarith) hr.le
    linarith
  have hP₀3 : 2 * (1 + z₁.im + ρ) / r ≤ P₀ := by
    have : 0 ≤ 2 * topHeight / r := div_nonneg (by linarith) hr.le
    have : 0 ≤ topHeight / y₀ := div_nonneg ht0.le hy₀.le
    linarith
  obtain ⟨p, hpp, hpbig, hpN⟩ := Nat.exists_prime_gt_modEq_one ⌈P₀⌉₊ hN.ne'
  have hpP : P₀ < p := (Nat.le_ceil P₀).trans_lt (by exact_mod_cast hpbig)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hpt1 : topHeight < p * (r / 2) := by
    have h1 : 2 * topHeight / r < p := hP₀1.trans_lt hpP
    rw [div_lt_iff₀ hr] at h1
    linarith
  have hpt2 : topHeight < p * y₀ := by
    have h1 : topHeight / y₀ < p := hP₀2.trans_lt hpP
    rw [div_lt_iff₀ hy₀] at h1
    linarith
  have hpt3 : (1 + z₁.im + ρ) / p < r / 2 := by
    have h1 : 2 * (1 + z₁.im + ρ) / r < p := hP₀3.trans_lt hpP
    rw [div_lt_iff₀ hr] at h1
    rw [div_lt_iff₀ hp0]
    linarith
  -- transport by `p` on the half-disc side
  obtain ⟨β, hβ⟩ := exists_heckeAffine_partner F k p hpp.pos (hB1 p hpp hpN) hHo hHc ⟨w₀, hw₀⟩
    (u := fun w => w) (v := v) differentiableOn_id hv (fun w hw => hw.2) hvU
    (fun w hw => (hvf w hw).symm) none
  cases β with
  | none =>
    -- `v` would be real affine
    have hrel : ∀ w ∈ H, qSeriesExt (F.c k) (affC (p : ℝ) 0 w) =
        qSeriesExt (F.c k) (affC (p : ℝ) 0 (v w)) := fun w hw => hβ w hw
    have htop : ∀ w ∈ H, topHeight ≤ (affC (p : ℝ) 0 (v w)).im := by
      intro w hw
      rw [affC_im]
      have := hvim w hw
      nlinarith
    have hw₀top : topHeight < (affC (p : ℝ) 0 w₀).im := by
      rw [affC_im, hw₀im]
      exact hpt1
    obtain ⟨a, b, ha, hab⟩ := exists_affC_eqOn_of_top hc hHo hHc hv hp0 hp0 hrel htop hw₀
      hw₀top
    set s : ℝ := min (r / 2) (y₀ / (2 * a)) with hs
    have hs0 : 0 < s := lt_min (half_pos hr) (div_pos hy₀ (by linarith))
    have hsr : s ≤ r / 2 := min_le_left _ _
    have hsa : s ≤ y₀ / (2 * a) := min_le_right _ _
    set ws : ℂ := (x₁ : ℂ) + (s : ℂ) * Complex.I with hws
    have hwsH : ws ∈ H := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, hws, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
        linarith
      · change 0 < ws.im
        simpa [hws] using hs0
    have h1 := hvim ws hwsH
    rw [hab ws hwsH, affC_im] at h1
    have hwsim : ws.im = s := by simp [hws]
    rw [hwsim] at h1
    have h2 : a * s ≤ y₀ / 2 := by
      have := mul_le_mul_of_nonneg_left hsa ha.le
      rw [show a * (y₀ / (2 * a)) = y₀ / 2 by field_simp] at this
      exact this
    linarith
  | some j =>
    -- an injective self-map of `H` into a small closed disc
    have hP : (p : ℝ) ≠ 0 := hp0.ne'
    set sj : ℝ := (z₁.re + ((j : ℕ) : ℝ)) / p with hsj
    set m : ℤ := ⌊(p : ℝ) * x₁ - sj⌋ with hm
    have hm1 : (m : ℝ) ≤ p * x₁ - sj := Int.floor_le _
    have hm2 : (p : ℝ) * x₁ - sj < m + 1 := Int.lt_floor_add_one _
    set a₁ : ℝ := (p : ℝ)⁻¹ * (p : ℝ)⁻¹ with ha₁
    set b₁ : ℝ := (p : ℝ)⁻¹ * (((j : ℕ) : ℝ) / p) + (m : ℝ) / p with hb₁
    have ha₁0 : 0 < a₁ := mul_pos (inv_pos.mpr hp0) (inv_pos.mpr hp0)
    have hkey : ∀ ζ : ℂ, affC (p : ℝ) 0 (affC a₁ b₁ ζ) =
        heckeAffine p (some j) ζ + ((m : ℤ) : ℂ) := by
      intro ζ
      have hPc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
      simp only [affC, heckeAffine, heckeDil, heckeTr, ha₁, hb₁]
      push_cast
      field_simp
      ring
    set G : ℂ → ℂ := fun z => qSeriesExt (F.c k) (affC (p : ℝ) 0 z) with hG
    have hGτ : ∀ w ∈ H, G (affC a₁ b₁ (v w)) = G w := by
      intro w hw
      simp only [hG]
      rw [hkey, qSeriesExt_add_intCast _ (heckeAffine_im_pos hpp.pos _ (hvU w hw))]
      exact (hβ w hw).symm
    -- the image disc `K`
    set c₁ : ℂ := affC a₁ b₁ z₁ with hc₁
    set K : Set ℂ := Metric.closedBall c₁ (a₁ * ρ) with hK
    have hτK : ∀ w ∈ H, affC a₁ b₁ (v w) ∈ K := by
      intro w hw
      rw [hK, Metric.mem_closedBall, dist_eq_norm, hc₁, norm_affC_sub_affC,
        abs_of_pos ha₁0]
      have := hvK w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left this ha₁0.le
    have hc₁re : c₁.re - x₁ = (p : ℝ)⁻¹ * (sj + m - p * x₁) := by
      rw [hc₁, affC_re, ha₁, hb₁, hsj]
      field_simp
      ring
    have hc₁im : c₁.im = a₁ * z₁.im := by rw [hc₁, affC_im]
    have hc₁dist : ‖c₁ - x₁‖ ≤ (p : ℝ)⁻¹ + a₁ * z₁.im := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have hre : (c₁ - x₁).re = c₁.re - x₁ := by simp
      have him : (c₁ - x₁).im = c₁.im := by simp
      rw [hre, him, hc₁re, hc₁im, abs_mul, abs_of_pos (inv_pos.mpr hp0),
        abs_of_pos (mul_pos ha₁0 hz₁im)]
      have h1 : |sj + m - p * x₁| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hp0).le
      linarith
    have ha₁p : a₁ ≤ (p : ℝ)⁻¹ := by
      rw [ha₁]
      have := inv_le_one_of_one_le₀ hp1
      have hpinv := (inv_pos.mpr hp0).le
      nlinarith
    have hKball : ∀ ζ ∈ K, ‖ζ - x₁‖ < r / 2 := by
      intro ζ hζ
      rw [hK, Metric.mem_closedBall, dist_eq_norm] at hζ
      have h1 : ‖ζ - x₁‖ ≤ ‖ζ - c₁‖ + ‖c₁ - x₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h2 : a₁ * ρ + a₁ * z₁.im ≤ (p : ℝ)⁻¹ * (ρ + z₁.im) := by
        have := mul_le_mul_of_nonneg_right ha₁p (by linarith : (0 : ℝ) ≤ ρ + z₁.im)
        linarith
      have h3 : (p : ℝ)⁻¹ + (p : ℝ)⁻¹ * (ρ + z₁.im) = (1 + z₁.im + ρ) / p := by
        field_simp
        ring
      linarith
    have hKim : ∀ ζ ∈ K, 0 < ζ.im := by
      intro ζ hζ
      rw [hK, Metric.mem_closedBall, dist_eq_norm] at hζ
      have h1 := Complex.abs_im_le_norm (ζ - c₁)
      rw [Complex.sub_im] at h1
      have h2 := (abs_le.mp (h1.trans hζ)).1
      rw [hc₁im] at h2
      have h3 : 0 < a₁ * (z₁.im - ρ) := mul_pos ha₁0 (by linarith)
      linarith
    have hKH : K ⊆ H := fun ζ hζ =>
      ⟨by rw [Metric.mem_ball, dist_eq_norm]; linarith [hKball ζ hζ], hKim ζ hζ⟩
    have hw₀K : w₀ ∉ K := fun h => by
      have := hKball w₀ h
      rw [hw₀dist] at this
      exact lt_irrefl _ this
    have hGd : DifferentiableOn ℂ G upperHalfPlaneSet :=
      (differentiableOn_qSeriesExt hc).comp (differentiable_affC _ _).differentiableOn
        (fun z hz => affC_im_pos hp0 0 hz)
    have hconst := eq_of_comp_eq_of_mapsTo_compact isOpen_upperHalfPlaneSet
      (convex_halfSpace_im_gt 0).isPreconnected hGd (fun z hz => hz.2)
      (isCompact_closedBall c₁ (a₁ * ρ)) hKH hτK (injOn_affC_comp ha₁0.ne' hinj) hGτ hw₀ hw₀K
    -- `f` would be constant
    obtain ⟨z, w, hz, hw, hne⟩ := qSeriesExt_exists_ne hc
    have hscale : ∀ ζ : ℂ, affC (p : ℝ) 0 (affC (p : ℝ)⁻¹ 0 ζ) = ζ := fun ζ => by
      rw [affC_affC, mul_inv_cancel₀ hP, mul_zero, add_zero, affC_one_zero]
    have hz' := hconst (affC (p : ℝ)⁻¹ 0 z) (affC_im_pos (inv_pos.mpr hp0) 0 hz)
    have hw' := hconst (affC (p : ℝ)⁻¹ 0 w) (affC_im_pos (inv_pos.mpr hp0) 0 hw)
    simp only [hG, hscale] at hz' hw'
    exact hne (hz'.trans hw'.symm)

end VOA.Moonshine.ConwayNorton
