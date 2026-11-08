/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroPairing
import VOA.Moonshine.MoonshineCNGenusZeroAnalytic

/-!
# Genus zero on the abstract interface: Hecke partners on connected domains

Partner uniqueness and pairing on connected domains (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`), written in the coordinates of `ℂ`.

* `affC a b` is the real affine map `z ↦ a z + b`; `heckeAffine p β` (`β : Option (Fin p)`) is the
  Hecke map `z ↦ p z` (`β = none`) or `z ↦ (z + j)/p` (`β = some j`), i.e. `Δ(p)`.
* `qSeriesExt c = qSeriesFun c ∘ ofComplex` is the `q`-series read on `ℂ`; it is holomorphic on the
  upper half-plane (`differentiableOn_qSeriesExt`) and `1`-periodic (`qSeriesExt_add_intCast`).
* `topHeight` is the height of the top-injectivity lemma (`exists_height_injective`), and
  `exists_int_of_qSeriesExt_eq` is top injectivity on `ℂ`.
* `heckeAffine_pairing` (pointwise Hecke pairing): `f z = f w` gives, for every `M ∈ Δ(p)`,
  some `β ∈ Δ(p)` with `f (M z) = f (β w)` (conditional on the prime Hecke identity at `p`).
* `heckeAffine_eq_of_frequently_eq` (partner uniqueness): if `f ∘ β = f ∘ β′` at points
  accumulating at a point of `ℍ`, then `β = β′` (no Hecke input; `p > 1`).
* `exists_heckeAffine_partner` (pairing on connected domains): for holomorphic `u, v : D → ℍ`
  on a connected open `D` with `f ∘ u = f ∘ v`, and every `M ∈ Δ(p)`, one `β ∈ Δ(p)` serves on
  all of `D`: `f ∘ M ∘ u = f ∘ β ∘ v` on `D`. Both the target form (`u = α`, `v = id`) and the
  source form (`u = id`, `v = α`) of the blueprint are special cases, so no holomorphic inverse
  is needed.
* `exists_iterate_heckeAffine_partner` (pairing on connected domains, iterated):
  `f (p^n u z) = f (p^e v z + b)` on `D` with `e ∈ ℤ`, `|e| ≤ n`, `b ∈ ℝ`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Real affine maps of `ℂ` -/

/-- The real affine map `z ↦ a z + b` of `ℂ` (`a b : ℝ`). -/
noncomputable def affC (a b : ℝ) (z : ℂ) : ℂ := a * z + b

lemma affC_apply (a b : ℝ) (z : ℂ) : affC a b z = a * z + b := rfl

lemma affC_re (a b : ℝ) (z : ℂ) : (affC a b z).re = a * z.re + b := by
  simp [affC]

lemma affC_im (a b : ℝ) (z : ℂ) : (affC a b z).im = a * z.im := by
  simp [affC]

lemma affC_affC (a b a' b' : ℝ) (z : ℂ) :
    affC a b (affC a' b' z) = affC (a * a') (a * b' + b) z := by
  simp only [affC]
  push_cast
  ring

lemma affC_one_zero (z : ℂ) : affC 1 0 z = z := by
  simp [affC]

lemma affC_inv_affC {a : ℝ} (ha : a ≠ 0) (b : ℝ) (z : ℂ) :
    affC a⁻¹ (-(b / a)) (affC a b z) = z := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [affC]
  push_cast
  field_simp
  ring

lemma affC_affC_inv {a : ℝ} (ha : a ≠ 0) (b : ℝ) (z : ℂ) :
    affC a b (affC a⁻¹ (-(b / a)) z) = z := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [affC]
  push_cast
  field_simp
  ring

lemma differentiable_affC (a b : ℝ) : Differentiable ℂ (affC a b) := by
  unfold affC
  fun_prop

lemma continuous_affC (a b : ℝ) : Continuous (affC a b) :=
  (differentiable_affC a b).continuous

lemma affC_im_pos {a : ℝ} (ha : 0 < a) (b : ℝ) {z : ℂ} (hz : 0 < z.im) : 0 < (affC a b z).im := by
  rw [affC_im]
  exact mul_pos ha hz

lemma norm_affC_sub_le (a b : ℝ) (z : ℂ) : ‖affC a b z - z‖ ≤ |a - 1| * ‖z‖ + |b| := by
  have h : affC a b z - z = ((a - 1 : ℝ) : ℂ) * z + (b : ℂ) := by
    simp only [affC]
    push_cast
    ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

/-! ### The Hecke maps `Δ(p)` as affine maps -/

/-- Dilation of the Hecke map `β ∈ Δ(p)`: `p` for `z ↦ p z`, `1/p` for `z ↦ (z + j)/p`. -/
noncomputable def heckeDil (p : ℕ) : Option (Fin p) → ℝ
  | none => p
  | some _ => (p : ℝ)⁻¹

/-- Translation part of the Hecke map `β ∈ Δ(p)`: `0` for `z ↦ p z`, `j/p` for `z ↦ (z + j)/p`. -/
noncomputable def heckeTr (p : ℕ) : Option (Fin p) → ℝ
  | none => 0
  | some j => ((j : ℕ) : ℝ) / p

/-- The Hecke map `β ∈ Δ(p)` acting on `ℂ`: `z ↦ p z` (`β = none`), `z ↦ (z + j)/p`
(`β = some j`). -/
noncomputable def heckeAffine (p : ℕ) (β : Option (Fin p)) : ℂ → ℂ :=
  affC (heckeDil p β) (heckeTr p β)

lemma heckeDil_pos {p : ℕ} (hp : 0 < p) (β : Option (Fin p)) : 0 < heckeDil p β := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  cases β with
  | none => exact hp'
  | some _ => exact inv_pos.mpr hp'

lemma heckeDil_eq_zpow (p : ℕ) (β : Option (Fin p)) :
    ∃ e : ℤ, |e| ≤ 1 ∧ heckeDil p β = (p : ℝ) ^ e := by
  cases β with
  | none => exact ⟨1, by norm_num, by simp [heckeDil]⟩
  | some _ => exact ⟨-1, by norm_num, by simp [heckeDil]⟩

lemma heckeAffine_im_pos {p : ℕ} (hp : 0 < p) (β : Option (Fin p)) {z : ℂ} (hz : 0 < z.im) :
    0 < (heckeAffine p β z).im :=
  affC_im_pos (heckeDil_pos hp β) _ hz

lemma heckeAffine_some_coe {p : ℕ} (hp : 0 < p) (j : Fin p) (τ : ℍ) :
    heckeAffine p (some j) τ = ((heckePoint 1 p j one_pos hp τ : ℍ) : ℂ) := by
  rw [coe_heckePoint]
  simp only [heckeAffine, affC, heckeDil, heckeTr]
  push_cast
  ring

lemma heckeAffine_none_coe {p : ℕ} (hp : 0 < p) (τ : ℍ) :
    heckeAffine p none τ = ((heckePoint p 1 0 hp one_pos τ : ℍ) : ℂ) := by
  rw [coe_heckePoint]
  simp only [heckeAffine, affC, heckeDil, heckeTr]
  push_cast
  ring

/-! ### The `q`-series read on `ℂ` -/

/-- The `q`-series `qSeriesFun c` read on `ℂ` (meaningful on the upper half-plane). -/
noncomputable def qSeriesExt (c : ℕ → ℂ) : ℂ → ℂ :=
  qSeriesFun c ∘ ofComplex

lemma qSeriesExt_coe (c : ℕ → ℂ) (τ : ℍ) : qSeriesExt c τ = qSeriesFun c τ :=
  comp_ofComplex _ τ

lemma qSeriesExt_of_im_pos (c : ℕ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    qSeriesExt c z = qSeriesFun c ⟨z, hz⟩ :=
  comp_ofComplex_of_im_pos _ z hz

lemma differentiableOn_qSeriesExt {c : ℕ → ℂ} (hc : IsJDominated c) :
    DifferentiableOn ℂ (qSeriesExt c) upperHalfPlaneSet :=
  mdifferentiable_iff.mp (mdifferentiable_qSeriesFun hc)

/-- `qSeriesExt c` is `1`-periodic on the upper half-plane. -/
lemma qSeriesExt_add_intCast (c : ℕ → ℂ) {z : ℂ} (hz : 0 < z.im) (n : ℤ) :
    qSeriesExt c (z + n) = qSeriesExt c z := by
  have hz' : 0 < (z + n).im := by simpa using hz
  rw [qSeriesExt_of_im_pos c hz', qSeriesExt_of_im_pos c hz]
  have hq : qPar ⟨z + n, hz'⟩ = qPar ⟨z, hz⟩ := by
    simp only [qPar, Function.Periodic.qParam, Complex.ofReal_one, div_one]
    change Complex.exp (2 * π * Complex.I * (z + n)) = Complex.exp (2 * π * Complex.I * z)
    rw [mul_add, Complex.exp_add, mul_comm (2 * π * Complex.I) (n : ℂ),
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [qSeriesFun, hq]

/-! ### The top height -/

/-- The height of the top-injectivity lemma (`exists_height_injective`): above it, every
`J`-dominated `q`-series is injective modulo `ℤ`. -/
noncomputable def topHeight : ℝ :=
  Classical.choose exists_height_injective

lemma topHeight_pos : 0 < topHeight :=
  (Classical.choose_spec exists_height_injective).1

/-- **Top injectivity on `ℂ`**: equal values at two points above `topHeight` force the points
to differ by an integer. -/
lemma exists_int_of_qSeriesExt_eq {c : ℕ → ℂ} (hc : IsJDominated c) {z w : ℂ}
    (hz : topHeight ≤ z.im) (hw : topHeight ≤ w.im) (h : qSeriesExt c z = qSeriesExt c w) :
    ∃ n : ℤ, z = w + n := by
  have hz0 : 0 < z.im := topHeight_pos.trans_le hz
  have hw0 : 0 < w.im := topHeight_pos.trans_le hw
  rw [qSeriesExt_of_im_pos c hz0, qSeriesExt_of_im_pos c hw0] at h
  exact (Classical.choose_spec exists_height_injective).2 c hc ⟨z, hz0⟩ ⟨w, hw0⟩ hz hw h

/-! ### Pointwise pairing -/

section Pairing

variable {N : ℕ} (F : ReplicableFamily N) (k p : ℕ) (hp : 0 < p)

/-- **Pointwise Hecke pairing on `ℍ`** in affine form. -/
theorem heckeAffine_pairing_coe (hB1 : PrimeHeckeIdentityAt F k p hp) {τ σ : ℍ}
    (h : qSeriesFun (F.c k) τ = qSeriesFun (F.c k) σ) (M : Option (Fin p)) :
    ∃ β : Option (Fin p), qSeriesExt (F.c k) (heckeAffine p M τ) =
      qSeriesExt (F.c k) (heckeAffine p β σ) := by
  cases M with
  | none =>
    rcases hecke_pairing_scale F k p hp hB1 h with ⟨j', hj', he⟩ | he
    · refine ⟨some ⟨j', hj'⟩, ?_⟩
      rw [heckeAffine_none_coe hp, heckeAffine_some_coe hp, qSeriesExt_coe, qSeriesExt_coe]
      exact he
    · refine ⟨none, ?_⟩
      rw [heckeAffine_none_coe hp, heckeAffine_none_coe hp, qSeriesExt_coe, qSeriesExt_coe]
      exact he
  | some j =>
    rcases hecke_pairing_shift F k p hp hB1 h j.isLt with ⟨j', hj', he⟩ | he
    · refine ⟨some ⟨j', hj'⟩, ?_⟩
      rw [heckeAffine_some_coe hp, heckeAffine_some_coe hp, qSeriesExt_coe, qSeriesExt_coe]
      exact he
    · refine ⟨none, ?_⟩
      rw [heckeAffine_some_coe hp, heckeAffine_none_coe hp, qSeriesExt_coe, qSeriesExt_coe]
      exact he

/-- **Pointwise Hecke pairing** on `ℂ`: if `f z = f w` (both in the upper half-plane), every
`M ∈ Δ(p)` has a partner `β ∈ Δ(p)` with `f (M z) = f (β w)`. -/
theorem heckeAffine_pairing (hB1 : PrimeHeckeIdentityAt F k p hp) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) (h : qSeriesExt (F.c k) z = qSeriesExt (F.c k) w) (M : Option (Fin p)) :
    ∃ β : Option (Fin p), qSeriesExt (F.c k) (heckeAffine p M z) =
      qSeriesExt (F.c k) (heckeAffine p β w) :=
  heckeAffine_pairing_coe F k p hp hB1 (τ := ⟨z, hz⟩) (σ := ⟨w, hw⟩)
    (by rwa [← qSeriesExt_of_im_pos, ← qSeriesExt_of_im_pos]) M

/-! ### Pairing on connected domains -/

/-- **Pairing on connected domains**. Let `u, v` be holomorphic on a connected open set `D`,
with values in the upper half-plane and `f ∘ u = f ∘ v` on `D`. For every `M ∈ Δ(p)` a single
`β ∈ Δ(p)` satisfies `f (M (u z)) = f (β (v z))` for all `z ∈ D`.

Proof: pointwise pairing at every point, pigeonhole on the finite set `Δ(p)` along a punctured
neighbourhood of one point, and the identity theorem on `D`. -/
theorem exists_heckeAffine_partner (hB1 : PrimeHeckeIdentityAt F k p hp) {D : Set ℂ}
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hDn : D.Nonempty) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u D) (hv : DifferentiableOn ℂ v D)
    (huU : ∀ z ∈ D, 0 < (u z).im) (hvU : ∀ z ∈ D, 0 < (v z).im)
    (huv : ∀ z ∈ D, qSeriesExt (F.c k) (u z) = qSeriesExt (F.c k) (v z)) (M : Option (Fin p)) :
    ∃ β : Option (Fin p), ∀ z ∈ D,
      qSeriesExt (F.c k) (heckeAffine p M (u z)) = qSeriesExt (F.c k) (heckeAffine p β (v z)) := by
  obtain ⟨z₀, hz₀⟩ := hDn
  have hev : ∀ᶠ z in 𝓝[≠] z₀, ∃ β : Option (Fin p),
      qSeriesExt (F.c k) (heckeAffine p M (u z)) = qSeriesExt (F.c k) (heckeAffine p β (v z)) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hDo.mem_nhds hz₀)] with z hz
    exact heckeAffine_pairing F k p hp hB1 (huU z hz) (hvU z hz) (huv z hz) M
  obtain ⟨β, hβ⟩ := Filter.frequently_exists.mp hev.frequently
  refine ⟨β, fun z hz => ?_⟩
  have hc := F.isJDominated k
  have hA : ∀ (γ : Option (Fin p)) (w : ℂ → ℂ), DifferentiableOn ℂ w D →
      (∀ z ∈ D, 0 < (w z).im) →
      AnalyticOnNhd ℂ (qSeriesExt (F.c k) ∘ heckeAffine p γ ∘ w) D := by
    intro γ w hw hwU
    exact ((differentiableOn_qSeriesExt hc).comp
      ((differentiable_affC _ _).comp_differentiableOn hw)
      (fun z hz => heckeAffine_im_pos hp γ (hwU z hz))).analyticOnNhd hDo
  exact (hA M u hu huU).eqOn_of_preconnected_of_frequently_eq (hA β v hv hvU) hDc hz₀ hβ hz

/-- **Iterated pairing on connected domains.** Under the hypotheses of
`exists_heckeAffine_partner` (at the fixed prime `p`), for every `n` there are `e ∈ ℤ` with
`|e| ≤ n` and `b ∈ ℝ` such that `f (p^n · u z) = f (p^e · v z + b)` on `D`. -/
theorem exists_iterate_heckeAffine_partner (hB1 : PrimeHeckeIdentityAt F k p hp) {D : Set ℂ}
    (hDo : IsOpen D) (hDc : IsPreconnected D) (hDn : D.Nonempty) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u D) (hv : DifferentiableOn ℂ v D)
    (huU : ∀ z ∈ D, 0 < (u z).im) (hvU : ∀ z ∈ D, 0 < (v z).im)
    (huv : ∀ z ∈ D, qSeriesExt (F.c k) (u z) = qSeriesExt (F.c k) (v z)) (n : ℕ) :
    ∃ (e : ℤ) (b : ℝ), |e| ≤ n ∧ ∀ z ∈ D,
      qSeriesExt (F.c k) (affC ((p : ℝ) ^ n) 0 (u z)) =
        qSeriesExt (F.c k) (affC ((p : ℝ) ^ e) b (v z)) := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  induction n with
  | zero =>
    refine ⟨0, 0, by simp, fun z hz => ?_⟩
    simpa [affC_one_zero] using huv z hz
  | succ n ih =>
    obtain ⟨e, b, he, h⟩ := ih
    obtain ⟨β, hβ⟩ := exists_heckeAffine_partner F k p hp hB1 hDo hDc hDn
      ((differentiable_affC _ _).comp_differentiableOn hu)
      ((differentiable_affC _ _).comp_differentiableOn hv)
      (fun z hz => affC_im_pos (pow_pos hp' n) 0 (huU z hz))
      (fun z hz => affC_im_pos (zpow_pos hp' e) b (hvU z hz)) h none
    obtain ⟨e', he', hβe⟩ := heckeDil_eq_zpow p β
    refine ⟨e' + e, heckeDil p β * b + heckeTr p β, ?_, fun z hz => ?_⟩
    · have h1 := abs_add_le e' e
      push_cast
      linarith
    · have h1 := hβ z hz
      simp only [Function.comp_apply, heckeAffine, affC_affC] at h1
      have h2 : heckeDil p none * (p : ℝ) ^ n = (p : ℝ) ^ (n + 1) := by
        simp only [heckeDil]
        ring
      have h3 : heckeDil p β * (p : ℝ) ^ e = (p : ℝ) ^ (e' + e) := by
        rw [hβe, zpow_add₀ hp'.ne']
      have h4 : heckeDil p none * 0 + heckeTr p none = 0 := by
        simp [heckeTr]
      rw [h2, h3, h4] at h1
      exact h1

end Pairing

/-! ### Partner uniqueness -/

/-- **Partner uniqueness**. For a `J`-dominated `q`-series `f` and `p > 1`, if
`f ∘ β = f ∘ β′` at points accumulating at a point of the upper half-plane, then `β = β′`.

Proof: by the identity theorem `f ∘ β = f ∘ β′` on the whole upper half-plane; at `z = i y`, `y`
large, both `β z` and `β′ z` lie above `topHeight`, so they differ by an integer (top
injectivity): the imaginary parts force equal dilations and the real parts equal translations. -/
theorem heckeAffine_eq_of_frequently_eq {c : ℕ → ℂ} (hc : IsJDominated c) {p : ℕ} (hp1 : 1 < p)
    {β β' : Option (Fin p)} {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    (h : ∃ᶠ z in 𝓝[≠] z₀, qSeriesExt c (heckeAffine p β z) = qSeriesExt c (heckeAffine p β' z)) :
    β = β' := by
  have hp : 0 < p := by omega
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) < p := by linarith
  have hA : ∀ γ : Option (Fin p),
      AnalyticOnNhd ℂ (qSeriesExt c ∘ heckeAffine p γ) upperHalfPlaneSet := fun γ =>
    ((differentiableOn_qSeriesExt hc).comp (differentiable_affC _ _).differentiableOn
      (fun z hz => heckeAffine_im_pos hp γ hz)).analyticOnNhd isOpen_upperHalfPlaneSet
  have heq := (hA β).eqOn_of_preconnected_of_frequently_eq (hA β')
    (convex_halfSpace_im_gt 0).isPreconnected hz₀ h
  set y : ℝ := p * (topHeight + 1) with hy
  have hy0 : 0 < y := mul_pos hp0 (by linarith [topHeight_pos])
  have hyI : 0 < ((y : ℂ) * Complex.I).im := by simpa using hy0
  have hdil : ∀ γ : Option (Fin p), (p : ℝ)⁻¹ ≤ heckeDil p γ := by
    intro γ
    cases γ with
    | none => exact (inv_le_one_of_one_le₀ hp'.le).trans hp'.le
    | some _ => exact le_rfl
  have hyp : (p : ℝ)⁻¹ * y = topHeight + 1 := by
    rw [hy]
    field_simp
  have htop : ∀ γ : Option (Fin p), topHeight ≤ (heckeAffine p γ ((y : ℂ) * Complex.I)).im := by
    intro γ
    have him : (heckeAffine p γ ((y : ℂ) * Complex.I)).im = heckeDil p γ * y := by
      simp [heckeAffine, affC_im]
    rw [him]
    nlinarith [hdil γ]
  have key : qSeriesExt c (heckeAffine p β ((y : ℂ) * Complex.I)) =
      qSeriesExt c (heckeAffine p β' ((y : ℂ) * Complex.I)) := heq hyI
  obtain ⟨n, hn⟩ := exists_int_of_qSeriesExt_eq hc (htop β) (htop β') key
  have him : heckeDil p β * y = heckeDil p β' * y := by
    have := congrArg Complex.im hn
    simpa [heckeAffine, affC_im] using this
  have hre : heckeTr p β = heckeTr p β' + n := by
    have := congrArg Complex.re hn
    simpa [heckeAffine, affC] using this
  have hd : heckeDil p β = heckeDil p β' := mul_right_cancel₀ hy0.ne' him
  rcases β with _ | j <;> rcases β' with _ | j'
  · rfl
  · exfalso
    simp only [heckeDil] at hd
    have h1 : (p : ℝ) * (p : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    rw [← hd] at h1
    nlinarith
  · exfalso
    simp only [heckeDil] at hd
    have h1 : (p : ℝ) * (p : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    rw [hd] at h1
    nlinarith
  · simp only [heckeTr] at hre
    have h2 : ((j : ℕ) : ℝ) = (j' : ℕ) + n * p := by
      have := congrArg (· * (p : ℝ)) hre
      simp only [add_mul, div_mul_cancel₀ _ hp0.ne'] at this
      linarith
    have h3 : ((j : ℕ) : ℤ) = (j' : ℕ) + n * p := by exact_mod_cast h2
    have hj := j.isLt
    have hj' := j'.isLt
    have hjz : ((j : ℕ) : ℤ) < p := by exact_mod_cast hj
    have hjz' : ((j' : ℕ) : ℤ) < p := by exact_mod_cast hj'
    have hj0 : (0 : ℤ) ≤ (j : ℕ) := Int.natCast_nonneg _
    have hj0' : (0 : ℤ) ≤ (j' : ℕ) := Int.natCast_nonneg _
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with hn | hn | hn
      · exfalso
        have : n * (p : ℤ) ≤ -(p : ℤ) := by nlinarith
        linarith
      · exact hn
      · exfalso
        have : (p : ℤ) ≤ n * (p : ℤ) := by nlinarith
        linarith
    have h4 : (j : ℕ) = (j' : ℕ) := by
      rw [hn0, zero_mul, add_zero] at h3
      exact_mod_cast h3
    exact congrArg some (Fin.ext h4)

end VOA.Moonshine.ConwayNorton
