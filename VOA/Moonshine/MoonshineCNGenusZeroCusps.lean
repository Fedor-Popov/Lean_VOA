/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroDiscrete
import VOA.Moonshine.MoonshineCNGenusZeroTop
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Genus zero on the abstract interface: behaviour at the other cusps

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. Let `f = qSeriesFun c` be `J`-dominated,
`G = symmetryGroup f`, and assume property P for `f` (`hP`: equal values are related by `G`,
proved in `MoonshineCNGenusZeroCritical`). Let `δ ∈ GL(2, ℝ)` have determinant one, let
`δ (1 h; 0 1) δ⁻¹ ∈ G` for some `h > 0` (a parabolic element of `G` fixing `δ ∞`), and let
`δ ∞` not be `G`-equivalent to `∞` (`hother : ∀ γ ∈ G, (γ δ) 1 0 ≠ 0`). Then:

* **cusp separation** (`one_le_mul_lowerLeft_sq_of_mem`): `h · ((γ δ) 1 0)² ≥ 1` for all
  `γ ∈ G` (Shimizu's lemma applied to `(γ δ) T^h (γ δ)⁻¹ ∈ G`); more generally Shimizu's lemma
  for conjugates (`one_le_mul_abs_lowerLeft_of_conj`);
* **boundedness** (`exists_bound_comp_smul_of_other`): `f ∘ δ` is bounded on `Im τ ≥ Y`
  (large values are taken high up, property P and cusp separation);
* **the cusp value** (`cuspData_of_other`): `f ∘ δ` is `h`-periodic, holomorphic and bounded
  at `i∞`, so its cusp function is analytic at `0` and `f (δ τ)` tends to its value at `0`;
* **the cusp value is not attained** (`qSeriesFun_ne_of_tendsto_comp_smul`): open mapping
  at a point taking the value, property P and cusp separation;
* **cusps with equal values are equivalent**
  (`exists_mem_lowerLeft_eq_zero_of_tendsto_eq`): open mapping of the cusp function at `0`,
  property P and Shimizu's lemma for the conjugate of `G` by the second cusp.

Also: `|f| → ∞` at `i∞` (`tendsto_norm_qSeriesFun_atImInfty`) and the transfer
`hasCuspValue_of_tendsto_comp_smul` to the statement's `HasCuspValue`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix
open scoped MatrixGroups Manifold Real

variable {c : ℕ → ℂ}

/-! ### Imaginary parts and Shimizu's lemma for conjugates -/

/-- `Im (M τ) ≤ 1 / (c² Im τ)` for `det M = 1`, `c = M 1 0 ≠ 0`. -/
lemma im_smul_le_of_det_eq_one {M : GL (Fin 2) ℝ} (hM : M.det.val = 1) (h0 : M 1 0 ≠ 0)
    (τ : ℍ) : (M • τ).im ≤ 1 / (M 1 0 ^ 2 * τ.im) := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, hM, abs_one, one_mul]
  have h1 := c_mul_im_sq_le_normSq_denom M τ
  have hn : 0 < Complex.normSq (denom M τ) := Complex.normSq_pos.mpr (denom_ne_zero M τ)
  have hc2 : 0 < M 1 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  rw [div_le_div_iff₀ hn (mul_pos hc2 τ.im_pos)]
  have e : τ.im * (M 1 0 ^ 2 * τ.im) = (M 1 0 * τ.im) ^ 2 := by ring
  rw [e, one_mul]
  exact h1

lemma det_val_mul_eq_one {g h : GL (Fin 2) ℝ} (hg : g.det.val = 1) (hh : h.det.val = 1) :
    (g * h).det.val = 1 := by
  rw [map_mul, Units.val_mul, hg, hh, one_mul]

lemma det_val_inv_eq_one {g : GL (Fin 2) ℝ} (hg : g.det.val = 1) : (g⁻¹).det.val = 1 := by
  rw [map_inv, Units.val_inv_eq_inv_val, hg, inv_one]

/-- **Shimizu's lemma for a conjugate of the symmetry group.** If `δ T^h δ⁻¹ ∈ G` (`h > 0`,
`det δ > 0`) and `δ X δ⁻¹ ∈ G` with `det X = 1`, `X 1 0 ≠ 0`, then `1 ≤ h |X 1 0|`. -/
theorem one_le_mul_abs_lowerLeft_of_conj (hc : IsJDominated c) {δ : GL (Fin 2) ℝ}
    (hδ : 0 < δ.det.val) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c)) {X : GL (Fin 2) ℝ}
    (hX : X.det.val = 1) (hXG : δ * X * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hX0 : X 1 0 ≠ 0) : 1 ≤ h * |X 1 0| := by
  by_contra hlt
  rw [not_le] at hlt
  have hD0 : h * 1 ≠ 0 := by rw [mul_one]; exact hh.ne'
  have hDdet : 0 < (glUpperTri h 0 1 hD0).det.val := by
    rw [GeneralLinearGroup.val_det_apply, glUpperTri_val, det_fin_two_of]; simpa using hh
  have hδD : 0 < (δ * glUpperTri h 0 1 hD0).det.val := by
    rw [map_mul, Units.val_mul]; exact mul_pos hδ hDdet
  have hχ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => qSeriesFun c ((δ * glUpperTri h 0 1 hD0) • τ)) :=
    (mdifferentiable_qSeriesFun hc).comp (mdifferentiable_smul hδD)
  have hDT : glUpperTri h 0 1 hD0 * glUpperUnipotent 1 =
      glUpperUnipotent h * glUpperTri h 0 1 hD0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glUpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  have hXdet : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 1 := by rw [← glFinTwo_det_eq]; exact hX
  have hgdet : X 0 0 * X 1 1 - X 0 1 / h * (h * X 1 0) = 1 := by
    have e : X 0 1 / h * (h * X 1 0) = X 0 1 * X 1 0 := by field_simp
    rw [e]; exact hXdet
  have hDg : glUpperTri h 0 1 hD0 * glOfDetOne (X 0 0) (X 0 1 / h) (h * X 1 0) (X 1 1) hgdet =
      X * glUpperTri h 0 1 hD0 := by
    ext i j
    rw [glFinTwo_mul_apply, glFinTwo_mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, glUpperTri_val, of_apply,
        cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, glOfDetOne_apply_zero_zero,
        glOfDetOne_apply_zero_one, glOfDetOne_apply_one_zero, glOfDetOne_apply_one_one, zero_mul,
        mul_zero, add_zero, zero_add, mul_one, one_mul] <;>
      first | ring1 | field_simp
  have hT : ∀ τ : ℍ, qSeriesFun c ((δ * glUpperTri h 0 1 hD0) • (glUpperUnipotent 1 • τ)) =
      qSeriesFun c ((δ * glUpperTri h 0 1 hD0) • τ) := by
    intro τ
    have e : (δ * glUpperTri h 0 1 hD0) * glUpperUnipotent 1 =
        (δ * glUpperUnipotent h * δ⁻¹) * (δ * glUpperTri h 0 1 hD0) := by
      rw [mul_assoc, hDT]; group
    rw [← mul_smul, e, mul_smul, hpar.2]
  have hg : ∀ τ : ℍ, qSeriesFun c ((δ * glUpperTri h 0 1 hD0) •
      (glOfDetOne (X 0 0) (X 0 1 / h) (h * X 1 0) (X 1 1) hgdet • τ)) =
      qSeriesFun c ((δ * glUpperTri h 0 1 hD0) • τ) := by
    intro τ
    have e : (δ * glUpperTri h 0 1 hD0) * glOfDetOne (X 0 0) (X 0 1 / h) (h * X 1 0) (X 1 1)
        hgdet = (δ * X * δ⁻¹) * (δ * glUpperTri h 0 1 hD0) := by
      rw [mul_assoc, hDg]; group
    rw [← mul_smul, e, mul_smul, hXG.2]
  have hconst := eq_of_invariant_of_lowerLeft_abs_lt_one hχ (glOfDetOne_det _ _ _ _ _)
    (by rw [glOfDetOne_apply_one_zero]; exact mul_ne_zero hh.ne' hX0)
    (by rw [glOfDetOne_apply_one_zero, abs_mul, abs_of_pos hh]; exact hlt) hT hg
  obtain ⟨τ, σ, hne⟩ := qSeriesFun_exists_ne hc
  apply hne
  have e1 := hconst ((δ * glUpperTri h 0 1 hD0)⁻¹ • τ) ((δ * glUpperTri h 0 1 hD0)⁻¹ • σ)
  simpa only [smul_inv_smul] using e1

/-- **Cusp separation**: if `δ T^h δ⁻¹ ∈ G` and `(γ δ) 1 0 ≠ 0`, then `1 ≤ h ((γ δ) 1 0)²`. -/
theorem one_le_mul_lowerLeft_sq_of_mem (hc : IsJDominated c) {δ : GL (Fin 2) ℝ}
    (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c)) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ symmetryGroup (qSeriesFun c)) (h0 : (γ * δ) 1 0 ≠ 0) :
    1 ≤ h * (γ * δ) 1 0 ^ 2 := by
  have hM : (γ * δ).det.val = 1 :=
    det_val_mul_eq_one (det_val_eq_one_of_mem_symmetryGroup hγ) hδ
  have hY : (γ * δ) * glUpperUnipotent h * (γ * δ)⁻¹ ∈ symmetryGroup (qSeriesFun c) := by
    have e : (γ * δ) * glUpperUnipotent h * (γ * δ)⁻¹ =
        γ * (δ * glUpperUnipotent h * δ⁻¹) * γ⁻¹ := by group
    rw [e]
    exact (symmetryGroup _).mul_mem ((symmetryGroup _).mul_mem hγ hpar)
      ((symmetryGroup _).inv_mem hγ)
  rw [conj_glUpperUnipotent hM] at hY
  have hpos : 0 < h * (γ * δ) 1 0 ^ 2 :=
    mul_pos hh (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0)))
  have h1 := one_le_abs_lowerLeft_qSeriesFun hc hY
    (by rw [glOfDetOne_apply_one_zero]; exact neg_ne_zero.mpr hpos.ne')
  rwa [glOfDetOne_apply_one_zero, abs_neg, abs_of_pos hpos] at h1

/-- **Points with the value of `f ∘ δ` lie low** (property P plus cusp separation): if
`f z = f (δ τ)` then `Im z ≤ h / Im τ`. -/
theorem im_le_of_eq_comp_smul (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) {z τ : ℍ}
    (hz : qSeriesFun c z = qSeriesFun c (δ • τ)) : z.im ≤ h / τ.im := by
  obtain ⟨γ, hγ, hγz⟩ := hP z (δ • τ) hz
  have hγ' := (symmetryGroup (qSeriesFun c)).inv_mem hγ
  have hz' : z = (γ⁻¹ * δ) • τ := by rw [mul_smul, ← hγz, inv_smul_smul]
  have h0 := hother _ hγ'
  have hbound := one_le_mul_lowerLeft_sq_of_mem hc hδ hh hpar hγ' h0
  have hdet : (γ⁻¹ * δ).det.val = 1 :=
    det_val_mul_eq_one (det_val_eq_one_of_mem_symmetryGroup hγ') hδ
  have him := im_smul_le_of_det_eq_one hdet h0 τ
  rw [← hz'] at him
  have hτ := τ.im_pos
  have hc2 : 0 < (γ⁻¹ * δ) 1 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  refine him.trans ?_
  rw [div_le_div_iff₀ (mul_pos hc2 hτ) hτ]
  nlinarith

/-! ### Boundedness and the cusp value -/

/-- **`f ∘ δ` is bounded near `i∞`** when `δ ∞` is not equivalent to `∞`. -/
theorem exists_bound_comp_smul_of_other (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) :
    ∃ Y R : ℝ, ∀ τ : ℍ, Y ≤ τ.im → ‖qSeriesFun c (δ • τ)‖ < R := by
  obtain ⟨R, Y₀, hY₀, hlarge⟩ := largeValuesFromTop_qSeriesFun hc
  refine ⟨h / Y₀ + 1, R, fun τ hτ => ?_⟩
  by_contra hge
  obtain ⟨σ, hσY, hσ⟩ := hlarge _ (not_lt.mp hge)
  have him := im_le_of_eq_comp_smul hc hP hδ hh hpar hother hσ
  have hτ0 := τ.im_pos
  have h1 : Y₀ ≤ h / τ.im := hσY.trans him
  rw [le_div_iff₀ hτ0] at h1
  have h2 : τ.im ≤ h / Y₀ := by rw [le_div_iff₀ hY₀]; linarith
  linarith

/-- `f ∘ δ` composed with `ofComplex` is `h`-periodic when `δ T^h δ⁻¹` is a symmetry. -/
lemma periodic_comp_smul_ofComplex {f : ℍ → ℂ} {δ : GL (Fin 2) ℝ} {h : ℝ}
    (hpar : ∀ τ : ℍ, f ((δ * glUpperUnipotent h * δ⁻¹) • τ) = f τ) :
    Function.Periodic ((fun τ : ℍ => f (δ • τ)) ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + h).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    have e1 : (⟨w + h, hw'⟩ : ℍ) = glUpperUnipotent h • (⟨w, hw⟩ : ℍ) := by
      ext; rw [coe_glUpperUnipotent_smul]
    have e2 : δ • (glUpperUnipotent h • (⟨w, hw⟩ : ℍ)) =
        (δ * glUpperUnipotent h * δ⁻¹) • (δ • (⟨w, hw⟩ : ℍ)) := by
      simp only [← mul_smul]; congr 1; group
    rw [e1, e2, hpar]
  · have hw' : (w + h).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      ofComplex_apply_of_im_nonpos hw']

/-- **The cusp data at an other cusp**: the cusp function of `f ∘ δ` (period `h`) is
analytic at `0`; `f (δ τ)` tends to its value at `0` as `Im τ → ∞`; and every nonzero `q` with
`‖q‖ < 1` is the `q`-parameter of a point `τ` with `Im τ = -h / (2π) · log ‖q‖`, where the cusp
function equals `f (δ τ)`. -/
theorem cuspData_of_other (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) :
    AnalyticAt ℂ (cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ))) 0 ∧
      Tendsto (fun τ : ℍ => qSeriesFun c (δ • τ)) atImInfty
        (𝓝 (cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) 0)) ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → ∃ τ : ℍ, τ.im = -h / (2 * π) * Real.log ‖q‖ ∧
        cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) q = qSeriesFun c (δ • τ) := by
  have hper := periodic_comp_smul_ofComplex (f := qSeriesFun c) hpar.2
  have hδpos : 0 < δ.det.val := by rw [hδ]; exact one_pos
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => qSeriesFun c (δ • τ)) :=
    (mdifferentiable_qSeriesFun hc).comp (mdifferentiable_smul hδpos)
  have hbdd : IsBoundedAtImInfty (fun τ : ℍ => qSeriesFun c (δ • τ)) := by
    obtain ⟨Y, R, hYR⟩ := exists_bound_comp_smul_of_other hc hP hδ hh hpar hother
    exact isBoundedAtImInfty_iff.mpr ⟨R, Y, fun τ hτ => (hYR τ hτ).le⟩
  have hA := analyticAt_cuspFunction_zero hh hper hhol hbdd
  refine ⟨hA, ?_, ?_⟩
  · have h1 := hA.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)
    refine h1.congr fun τ => ?_
    exact eq_cuspFunction τ hh.ne' hper
  · intro q hq0 hq1
    have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hq1 hq0
    refine ⟨⟨_, him⟩, Function.Periodic.im_invQParam h q, ?_⟩
    rw [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0, Function.comp_apply,
      ofComplex_apply_of_im_pos him]

/-! ### The cusp value is not attained -/

/-- **The value at an other cusp is not attained in `ℍ`**. -/
theorem qSeriesFun_ne_of_tendsto_comp_smul (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) {w : ℂ}
    (hw : Tendsto (fun τ : ℍ => qSeriesFun c (δ • τ)) atImInfty (𝓝 w)) (τ₀ : ℍ) :
    qSeriesFun c τ₀ ≠ w := by
  intro hτ₀
  have hgA := (differentiableOn_qSeriesExt hc).analyticOnNhd isOpen_upperHalfPlaneSet
  have hz0 : 0 < (τ₀ : ℂ).im := τ₀.im_pos
  have hopen : 𝓝 (qSeriesExt c τ₀) ≤ map (qSeriesExt c) (𝓝 (τ₀ : ℂ)) :=
    (hgA τ₀ hz0).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_eq_qSeriesExt hc hz0)
  set r : ℝ := (τ₀ : ℂ).im / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hU : qSeriesExt c '' Metric.ball (τ₀ : ℂ) r ∈ 𝓝 w := by
    rw [← hτ₀, ← qSeriesExt_coe]
    exact hopen (image_mem_map (Metric.ball_mem_nhds _ hr0))
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, h / r + 1 ≤ τ.im :=
    (atImInfty_mem _).mpr ⟨h / r + 1, fun τ hτ => hτ⟩
  obtain ⟨τ, ⟨z, hzU, hz⟩, hτbig⟩ := ((hw.eventually hU).and hev2).exists
  have hzim : r < z.im := by
    have h1 : |(z - (τ₀ : ℂ)).im| < r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hzU
      exact (Complex.abs_im_le_norm (z - τ₀)).trans_lt hzU
    rw [Complex.sub_im] at h1
    rw [abs_lt] at h1
    rw [hr] at h1 ⊢
    linarith
  have hz0' : 0 < z.im := hr0.trans hzim
  have hfz : qSeriesFun c ⟨z, hz0'⟩ = qSeriesFun c (δ • τ) := by
    rw [← qSeriesExt_of_im_pos c hz0']; exact hz
  have him := im_le_of_eq_comp_smul hc hP hδ hh hpar hother hfz
  have hτ0 := τ.im_pos
  have h1 : r < h / τ.im := hzim.trans_le him
  rw [lt_div_iff₀ hτ0] at h1
  have h2 : h / r < τ.im := by linarith
  rw [div_lt_iff₀ hr0] at h2
  linarith

/-! ### Cusps with the same value are equivalent -/

/-- **Equal cusp values force equivalent cusps**: if `f ∘ δ` and `f ∘ δ'` tend to the same
value `w` at `i∞` (both `δ ∞`, `δ' ∞` not equivalent to `∞`), then some `γ ∈ G` has
`(δ'⁻¹ γ δ) ∞ = ∞`, i.e. `γ (δ ∞) = δ' ∞`. -/
theorem exists_mem_lowerLeft_eq_zero_of_tendsto_eq (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ δ' : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) (hδ' : δ'.det.val = 1) {h h' : ℝ}
    (hh : 0 < h) (hh' : 0 < h')
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hpar' : δ' * glUpperUnipotent h' * δ'⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0)
    (hother' : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ') 1 0 ≠ 0) {w : ℂ}
    (hw : Tendsto (fun τ : ℍ => qSeriesFun c (δ • τ)) atImInfty (𝓝 w))
    (hw' : Tendsto (fun τ : ℍ => qSeriesFun c (δ' • τ)) atImInfty (𝓝 w)) :
    ∃ γ ∈ symmetryGroup (qSeriesFun c), (δ'⁻¹ * γ * δ) 1 0 = 0 := by
  obtain ⟨hA, hlim, hq⟩ := cuspData_of_other hc hP hδ hh hpar hother
  set Ψ := cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) with hΨ
  have hΨ0 : Ψ 0 = w := tendsto_nhds_unique hlim hw
  -- the cusp function is not locally constant at `0`
  have hnc : ¬ ∀ᶠ q in 𝓝 (0 : ℂ), Ψ q = Ψ 0 := by
    intro hev
    have h1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Ψ q = Ψ 0 := hev.filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ∈ Metric.ball (0 : ℂ) 1 :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have h3 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ≠ 0 := self_mem_nhdsWithin
    obtain ⟨q, hqc, hq1, hq0⟩ := (h1.and (h2.and h3)).exists
    rw [Metric.mem_ball, dist_zero_right] at hq1
    obtain ⟨τ, -, hτ⟩ := hq q hq0 hq1
    exact qSeriesFun_ne_of_tendsto_comp_smul hc hP hδ hh hpar hother hw (δ • τ)
      (by rw [← hτ, hqc, hΨ0])
  have hopen : 𝓝 w ≤ map Ψ (𝓝 0) := by
    rw [← hΨ0]; exact hA.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  -- a small disc in `q`
  set Y : ℝ := h * h' + 1 with hY
  set r : ℝ := min (1 / 2) (Real.exp (-(2 * π * Y / h))) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (Real.exp_pos _)
  have hU : Ψ '' Metric.ball (0 : ℂ) r ∈ 𝓝 w := hopen (image_mem_map (Metric.ball_mem_nhds _ hr0))
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im := (atImInfty_mem _).mpr ⟨1, fun τ hτ => hτ⟩
  obtain ⟨τ', ⟨q, hqr, hqτ'⟩, hτ'1⟩ := ((hw'.eventually hU).and hev2).exists
  rw [Metric.mem_ball, dist_zero_right] at hqr
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact qSeriesFun_ne_of_tendsto_comp_smul hc hP hδ' hh' hpar' hother' hw' (δ' • τ')
      (by rw [← hqτ', hΨ0])
  have hq1 : ‖q‖ < 1 := hqr.trans_le ((min_le_left _ _).trans (by norm_num))
  obtain ⟨τ, hτim, hτq⟩ := hq q hq0 hq1
  -- `Im τ > Y`
  have hτY : Y < τ.im := by
    have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hlog : Real.log ‖q‖ < -(2 * π * Y / h) := by
      rw [Real.log_lt_iff_lt_exp hqpos]
      exact hqr.trans_le (min_le_right _ _)
    have hpi : 0 < 2 * π := by positivity
    have e : h * (-(2 * π * Y / h)) = -(2 * π * Y) := by field_simp
    have h3 := mul_lt_mul_of_pos_left hlog hh
    rw [e] at h3
    rw [hτim, div_mul_eq_mul_div, lt_div_iff₀ hpi]
    linarith
  -- property P
  have hfeq : qSeriesFun c (δ • τ) = qSeriesFun c (δ' • τ') := by rw [← hτq, hqτ']
  obtain ⟨γ, hγ, hγτ⟩ := hP _ _ hfeq
  refine ⟨γ, hγ, ?_⟩
  by_contra hA0
  set A := δ'⁻¹ * γ * δ with hAdef
  have hAdet : A.det.val = 1 :=
    det_val_mul_eq_one (det_val_mul_eq_one (det_val_inv_eq_one hδ')
      (det_val_eq_one_of_mem_symmetryGroup hγ)) hδ
  have hAτ : A • τ = τ' := by
    rw [hAdef, mul_smul, mul_smul, hγτ, inv_smul_smul]
  -- Shimizu for the conjugate by `δ'`
  set X := A * glUpperUnipotent h * A⁻¹ with hX
  have hXdet : X.det.val = 1 :=
    det_val_mul_eq_one (det_val_mul_eq_one hAdet (glOfDetOne_det 1 h 0 1 (by ring)))
      (det_val_inv_eq_one hAdet)
  have hXG : δ' * X * δ'⁻¹ ∈ symmetryGroup (qSeriesFun c) := by
    have e : δ' * X * δ'⁻¹ = γ * (δ * glUpperUnipotent h * δ⁻¹) * γ⁻¹ := by
      rw [hX, hAdef]; group
    rw [e]
    exact (symmetryGroup _).mul_mem ((symmetryGroup _).mul_mem hγ hpar)
      ((symmetryGroup _).inv_mem hγ)
  have hX10 : X 1 0 = -(h * A 1 0 ^ 2) := by
    rw [hX, conj_glUpperUnipotent hAdet, glOfDetOne_apply_one_zero]
  have hA2 : 0 < A 1 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hA0))
  have hshim := one_le_mul_abs_lowerLeft_of_conj hc (by rw [hδ']; exact one_pos) hh' hpar'
    hXdet hXG (by rw [hX10]; exact neg_ne_zero.mpr (mul_pos hh hA2).ne')
  rw [hX10, abs_neg, abs_of_pos (mul_pos hh hA2)] at hshim
  -- `Im τ' ≤ 1 / (A₁₀² Im τ) ≤ h h' / Im τ < 1`
  have him := im_smul_le_of_det_eq_one hAdet hA0 τ
  rw [hAτ] at him
  have hτ0 := τ.im_pos
  have h1 : 1 / (A 1 0 ^ 2 * τ.im) ≤ h * h' / τ.im := by
    rw [div_le_div_iff₀ (mul_pos hA2 hτ0) hτ0]
    nlinarith
  have h2 : h * h' / τ.im < 1 := by
    rw [div_lt_one hτ0]; linarith
  linarith

/-! ### The cusp `∞` and transfer to `HasCuspValue` -/

/-- `‖f‖ → ∞` at `i∞`. -/
theorem tendsto_norm_qSeriesFun_atImInfty (hc : IsJDominated c) :
    Tendsto (fun τ : ℍ => ‖qSeriesFun c τ‖) atImInfty atTop := by
  have h1 : Tendsto (fun τ : ℍ => ‖(qPar τ)⁻¹‖ + -‖qSeriesFun c τ - (qPar τ)⁻¹‖) atImInfty
      atTop := by
    have h2 : Tendsto (fun τ : ℍ => -‖qSeriesFun c τ - (qPar τ)⁻¹‖) atImInfty (𝓝 0) := by
      simpa using ((tendsto_qSeriesFun_sub_inv_qPar hc).norm).neg
    exact tendsto_norm_inv_qPar_atTop.atTop_add h2
  refine tendsto_atTop_mono (fun τ => ?_) h1
  have h3 := norm_sub_norm_le (qPar τ)⁻¹ ((qPar τ)⁻¹ - qSeriesFun c τ)
  rw [sub_sub_cancel, norm_sub_rev] at h3
  linarith

/-- Transfer to the statement's `HasCuspValue`: if `f (δ τ) → w` at `i∞` (`det δ > 0`), then `f`
has cusp value `w` at `δ ∞` along every `γ` sending `∞` to `δ ∞`. -/
theorem hasCuspValue_of_tendsto_comp_smul {f : ℍ → ℂ} {δ : GL (Fin 2) ℝ} {w : ℂ}
    (hw : Tendsto (fun τ : ℍ => f (δ • τ)) atImInfty (𝓝 w)) :
    HasCuspValue f (δ • cuspInfty) w := by
  intro γ hγ
  have hu : (δ⁻¹ * γ) • (cuspInfty : OnePoint ℝ) = cuspInfty := by
    rw [mul_smul, hγ.2, inv_smul_smul]
  have hu0 : (δ⁻¹ * γ) 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hu
  have h1 := hw.comp (tendsto_smul_atImInfty hu0)
  refine h1.congr fun τ => ?_
  simp only [Function.comp_apply, ← mul_smul, mul_inv_cancel_left]

end VOA.Moonshine.ConwayNorton
