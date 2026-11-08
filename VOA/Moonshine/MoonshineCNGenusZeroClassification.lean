/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroFamilies
import VOA.Moonshine.MoonshineCNGenusZeroBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Genus zero on the abstract interface: classification of the global symmetries in the families

Second half of "local symmetries are real Möbius maps" (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`). Let `f` be a `J`-dominated `q`-series and `β` one of the
explicit solutions of the real linear ODE with `β(ℍ) ⊆ ℍ` and `f ∘ β = f` on `ℍ` (the output of
the global extension of a local symmetry, `forall_im_pos_and_eq_of_local`). No Hecke input is
used here; only the growth `‖f z − q⁻¹‖ ≤ jTail (Im z)` and top injectivity.

* exponential family `K e^{A z} + M₀` (`A ≠ 0`, `K ≠ 0`): impossible, it takes the value `M₀ − i`
  on `ℍ` (`false_of_exp_family`);
* logarithmic family `B log (z − c) + K`: impossible, its imaginary part is constant on the vertical
  line through `c` while `f` grows there (`false_of_log_family`);
* affine family `B z + K`: `B = 1` and `K ∈ ℤ` (`exists_int_of_affine_family`);
* power family `K (z − c)^A + M₀` (`A ≠ 0`, `K ≠ 0`): `A = 1` with `K > 0` real, or `A = −1` with
  `K < 0` real (`power_family_cases`). Steps: positivity of `Im (K e^{i A θ})` on `0 < θ < π`
  forces `|A| ≤ 1` (`abs_le_one_of_sin_pos`); `0 < A < 1` contradicts top injectivity on the
  vertical line through `c`; `−1 < A < 0` contradicts periodicity (`f (z + n) = f z`) between the
  vertical lines through `c` and `c ± 1`, where `β` is respectively unbounded upwards and convergent
  to a point of `ℍ`; `A = ±1` gives the real-coefficient conditions.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Growth of `qSeriesExt` -/

section Growth

variable {c : ℕ → ℂ}

lemma norm_qSeriesExt_le (hc : IsJDominated c) {z : ℂ} (hz : 0 < z.im) :
    ‖qSeriesExt c z‖ ≤ Real.exp (2 * π * z.im) + jTail z.im := by
  rw [qSeriesExt_of_im_pos c hz]
  have h1 := norm_qSeriesFun_sub_inv_qPar_le hc ⟨z, hz⟩
  have h2 := norm_inv_qPar ⟨z, hz⟩
  have h3 := norm_sub_norm_le (qSeriesFun c ⟨z, hz⟩) (qPar ⟨z, hz⟩)⁻¹
  change ‖qSeriesFun c ⟨z, hz⟩ - (qPar ⟨z, hz⟩)⁻¹‖ ≤ jTail z.im at h1
  change ‖(qPar ⟨z, hz⟩)⁻¹‖ = Real.exp (2 * Real.pi * z.im) at h2
  linarith

lemma le_norm_qSeriesExt (hc : IsJDominated c) {z : ℂ} (hz : 0 < z.im) :
    Real.exp (2 * π * z.im) - jTail z.im ≤ ‖qSeriesExt c z‖ := by
  rw [qSeriesExt_of_im_pos c hz]
  have h1 := norm_qSeriesFun_sub_inv_qPar_le hc ⟨z, hz⟩
  have h2 := norm_inv_qPar ⟨z, hz⟩
  have h3 := norm_sub_norm_le (qPar ⟨z, hz⟩)⁻¹ (qSeriesFun c ⟨z, hz⟩)
  rw [norm_sub_rev] at h3
  change ‖qSeriesFun c ⟨z, hz⟩ - (qPar ⟨z, hz⟩)⁻¹‖ ≤ jTail z.im at h1
  change ‖(qPar ⟨z, hz⟩)⁻¹‖ = Real.exp (2 * Real.pi * z.im) at h2
  linarith

/-- `f` is large high up: `C < ‖f z‖` once `Im z ≥ max 1 (C + jTail 1)`. -/
lemma lt_norm_qSeriesExt_of_le_im (hc : IsJDominated c) (C : ℝ) {z : ℂ} (hz1 : 1 ≤ z.im)
    (hzC : C + jTail 1 ≤ z.im) : C < ‖qSeriesExt c z‖ := by
  have hz : 0 < z.im := by linarith
  have h1 := le_norm_qSeriesExt hc hz
  have h2 : jTail z.im ≤ jTail 1 := jTail_le_of_le one_pos hz1
  have h3 : 2 * π * z.im + 1 ≤ Real.exp (2 * π * z.im) := by
    have := Real.add_one_le_exp (2 * π * z.im)
    linarith
  have h4 : z.im < 2 * π * z.im := by nlinarith [Real.pi_gt_three]
  linarith

end Growth

/-! ### The exponential family -/

/-- The exponential family does not map `ℍ` into `ℍ`. -/
theorem false_of_exp_family {A M₀ : ℝ} {K : ℂ} (hA : A ≠ 0) (hK : K ≠ 0)
    (hinto : ∀ z : ℂ, 0 < z.im → 0 < (K * Complex.exp (A * z) + M₀).im) : False := by
  have hIK : -Complex.I / K ≠ 0 := div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hK
  set w := Complex.log (-Complex.I / K) with hwdef
  have hw : Complex.exp w = -Complex.I / K := Complex.exp_log hIK
  set N₀ : ℕ := ⌈|w.im|⌉₊ + 1 with hN₀
  have hN₀w : |w.im| + 1 ≤ (N₀ : ℝ) := by
    rw [hN₀]
    push_cast
    linarith [Nat.le_ceil |w.im|]
  set n : ℤ := if 0 < A then (N₀ : ℤ) else -(N₀ : ℤ) with hn
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  set z : ℂ := (w + 2 * π * Complex.I * n) / A with hz
  have hwabs := neg_abs_le w.im
  have hwabs' := le_abs_self w.im
  have hzim : 0 < z.im := by
    rw [hz, Complex.div_ofReal_im]
    have him : (w + 2 * π * Complex.I * n).im = w.im + 2 * π * n := by simp
    rw [him]
    by_cases hA0 : 0 < A
    · rw [hn, if_pos hA0]
      apply div_pos _ hA0
      push_cast
      nlinarith [Real.pi_gt_three]
    · have hAneg : A < 0 := lt_of_le_of_ne (not_lt.mp hA0) hA
      rw [hn, if_neg hA0]
      apply div_pos_of_neg_of_neg _ hAneg
      push_cast
      nlinarith [Real.pi_gt_three]
  have hAz : (A : ℂ) * z = w + n * (2 * π * Complex.I) := by
    rw [hz]
    field_simp
  have hexp : Complex.exp (A * z) = -Complex.I / K := by
    rw [hAz, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hw]
  have h := hinto z hzim
  rw [hexp, show K * (-Complex.I / K) = -Complex.I by field_simp] at h
  norm_num at h

/-! ### The logarithmic family -/

/-- The logarithmic family is not a global symmetry. -/
theorem false_of_log_family {c : ℕ → ℂ} (hc : IsJDominated c) {B c₀ : ℝ} {K : ℂ}
    (hglob : ∀ z : ℂ, 0 < z.im → 0 < ((B : ℂ) * Complex.log (z - c₀) + K).im ∧
      qSeriesExt c ((B : ℂ) * Complex.log (z - c₀) + K) = qSeriesExt c z) : False := by
  have hline : ∀ y : ℝ, 0 < y →
      ((B : ℂ) * Complex.log (((c₀ : ℂ) + y * Complex.I) - c₀) + K).im = B * (π / 2) + K.im := by
    intro y hy
    rw [add_sub_cancel_left]
    have harg : Complex.arg ((y : ℂ) * Complex.I) = π / 2 := by
      rw [Complex.arg_real_mul _ hy, Complex.arg_I]
    rw [Complex.add_im, Complex.im_ofReal_mul, Complex.log_im, harg]
  have hzy : ∀ y : ℝ, ((c₀ : ℂ) + y * Complex.I).im = y := by
    intro y
    simp
  set h₀ := B * (π / 2) + K.im with hh₀
  have hh₀pos : 0 < h₀ := by
    have := (hglob ((c₀ : ℂ) + (1 : ℝ) * Complex.I) (by rw [hzy]; exact one_pos)).1
    rwa [hline 1 one_pos] at this
  set C := Real.exp (2 * π * h₀) + jTail h₀ with hC
  set y := max 1 (C + jTail 1) with hy
  have hy1 : 1 ≤ y := le_max_left _ _
  have hyC : C + jTail 1 ≤ y := le_max_right _ _
  have hy0 : 0 < y := by linarith
  obtain ⟨hpos, heq⟩ := hglob ((c₀ : ℂ) + y * Complex.I) (by rw [hzy]; exact hy0)
  have hbound := norm_qSeriesExt_le hc hpos
  rw [hline y hy0] at hbound
  have hlarge := lt_norm_qSeriesExt_of_le_im hc C (z := (c₀ : ℂ) + y * Complex.I)
    (by rw [hzy]; exact hy1) (by rw [hzy]; exact hyC)
  rw [← heq] at hlarge
  linarith

/-! ### The affine family -/

/-- An affine global symmetry is an integer translation. -/
theorem exists_int_of_affine_family {c : ℕ → ℂ} (hc : IsJDominated c) {B : ℝ} {K : ℂ}
    (hglob : ∀ z : ℂ, 0 < z.im → 0 < ((B : ℂ) * z + K).im ∧
      qSeriesExt c ((B : ℂ) * z + K) = qSeriesExt c z) :
    B = 1 ∧ ∃ n : ℤ, K = n := by
  have him : ∀ y : ℝ, ((B : ℂ) * ((y : ℂ) * Complex.I) + K).im = B * y + K.im := by
    intro y
    simp
  have hyI : ∀ y : ℝ, ((y : ℂ) * Complex.I).im = y := by
    intro y
    simp
  have hB : 0 < B := by
    rcases lt_trichotomy B 0 with hB | hB | hB
    · exfalso
      set y := (|K.im| + 1) / (-B) with hy
      have hy0 : 0 < y := div_pos (by positivity) (by linarith)
      have h1 := (hglob ((y : ℂ) * Complex.I) (by rw [hyI]; exact hy0)).1
      rw [him] at h1
      have h2 : B * y = -(|K.im| + 1) := by
        rw [hy, mul_div_assoc', div_eq_iff (neg_ne_zero.mpr hB.ne)]
        ring
      linarith [le_abs_self K.im]
    · exfalso
      set C := ‖qSeriesExt c K‖ with hC
      set y := max 1 (C + jTail 1) with hy
      have hy1 : 1 ≤ y := le_max_left _ _
      have hlarge := lt_norm_qSeriesExt_of_le_im hc C (z := (y : ℂ) * Complex.I)
        (by rw [hyI]; exact hy1) (by rw [hyI]; exact le_max_right _ _)
      have heq := (hglob ((y : ℂ) * Complex.I) (by rw [hyI]; linarith)).2
      rw [hB, Complex.ofReal_zero, zero_mul, zero_add] at heq
      rw [← heq] at hlarge
      exact lt_irrefl _ hlarge
    · exact hB
  set Y := max 1 (max topHeight ((topHeight - K.im) / B)) with hY
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hYt : topHeight ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYK : (topHeight - K.im) / B ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  have hrel : ∀ y : ℝ, Y ≤ y → ∃ n : ℤ, (B : ℂ) * ((y : ℂ) * Complex.I) + K =
      (y : ℂ) * Complex.I + n := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have heq := (hglob ((y : ℂ) * Complex.I) (by rw [hyI]; exact hy0)).2
    refine exists_int_of_qSeriesExt_eq hc ?_ (by rw [hyI]; linarith) heq
    rw [him]
    have : (topHeight - K.im) / B ≤ y := hYK.trans hy
    rw [div_le_iff₀ hB] at this
    linarith
  obtain ⟨n₁, h₁⟩ := hrel Y le_rfl
  obtain ⟨n₂, h₂⟩ := hrel (Y + 1) (by linarith)
  have hi1 : B * Y + K.im = Y := by
    have h := congrArg Complex.im h₁
    rw [him] at h
    simpa using h
  have hi2 : B * (Y + 1) + K.im = Y + 1 := by
    have h := congrArg Complex.im h₂
    rw [him] at h
    simpa using h
  have hB1 : B = 1 := by nlinarith
  have hK0 : K.im = 0 := by
    rw [hB1] at hi1
    linarith
  have hr1 : K.re = n₁ := by
    have h := congrArg Complex.re h₁
    simpa using h
  refine ⟨hB1, n₁, Complex.ext ?_ ?_⟩
  · simpa using hr1
  · simpa using hK0

/-! ### The power family: elementary facts -/

/-- `(r e^{iθ})^A = r^A e^{i A θ}` for `r > 0`, `-π < θ ≤ π`. -/
lemma ofReal_mul_exp_cpow {r θ : ℝ} (hr : 0 < r) (hθ1 : -π < θ) (hθ2 : θ ≤ π) (A : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ (A : ℂ) =
      ((r ^ A : ℝ) : ℂ) * Complex.exp ((A * θ : ℝ) * Complex.I) := by
  have hne : (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul hr (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using hθ1) (by simpa using hθ2), Real.rpow_def_of_pos hr,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `(i y)^A = y^A e^{i A π/2}` for `y > 0`. -/
lemma ofReal_mul_I_cpow {y : ℝ} (hy : 0 < y) (A : ℝ) :
    ((y : ℂ) * Complex.I) ^ (A : ℂ) =
      ((y ^ A : ℝ) : ℂ) * Complex.exp ((A * (π / 2) : ℝ) * Complex.I) := by
  have h := ofReal_mul_exp_cpow hy (θ := π / 2) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) A
  rwa [show ((π / 2 : ℝ) : ℂ) * Complex.I = π / 2 * Complex.I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I] at h

/-- `Im (K e^{i t}) = ‖K‖ sin (arg K + t)`. -/
lemma im_mul_exp_ofReal_mul_I (K : ℂ) (t : ℝ) :
    (K * Complex.exp (t * Complex.I)).im = ‖K‖ * Real.sin (Complex.arg K + t) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I K]
  rw [mul_assoc, ← Complex.exp_add,
    show (Complex.arg K : ℂ) * Complex.I + t * Complex.I = ((Complex.arg K + t : ℝ) : ℂ) *
      Complex.I by push_cast; ring,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `Im (K e^{i A θ}) > 0` for `0 < θ < π` when `K (z − c)^A + M₀` maps `ℍ` into `ℍ`. -/
lemma im_mul_exp_pos_of_power_into {c₀ A M₀ : ℝ} {K : ℂ}
    (hinto : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < π) : 0 < (K * Complex.exp ((A * θ : ℝ) * Complex.I)).im := by
  have hz : 0 < ((c₀ : ℂ) + (1 : ℝ) * Complex.exp (θ * Complex.I)).im := by
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.ofReal_one, one_mul,
      Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have h := hinto _ hz
  rw [add_sub_cancel_left, ofReal_mul_exp_cpow one_pos (by linarith [Real.pi_pos]) hθπ.le,
    Real.one_rpow, Complex.ofReal_one, one_mul, Complex.add_im, Complex.ofReal_im,
    add_zero] at h
  exact h

/-- Positivity of `sin (κ + A θ)` on `0 < θ < π` forces `|A| ≤ 1`. -/
lemma abs_le_one_of_sin_pos {κ A : ℝ}
    (hpos : ∀ θ : ℝ, 0 < θ → θ < π → 0 < Real.sin (κ + A * θ)) : |A| ≤ 1 := by
  by_contra hA
  have hA' : 1 < |A| := lt_of_not_ge hA
  have hπ := Real.pi_pos
  rcases lt_trichotomy A 0 with hneg | hzero | hposA
  · have hA1 : A < -1 := by
      rw [abs_of_neg hneg] at hA'
      linarith
    set m : ℤ := ⌈κ / π⌉ - 1 with hm
    have hc1 := Int.le_ceil (κ / π)
    have hc2 := Int.ceil_lt_add_one (κ / π)
    have hm1 : (m : ℝ) * π < κ := by
      have : (m : ℝ) < κ / π := by rw [hm]; push_cast; linarith
      rwa [lt_div_iff₀ hπ] at this
    have hm2 : κ - π ≤ (m : ℝ) * π := by
      have : κ / π - 1 ≤ (m : ℝ) := by rw [hm]; push_cast; linarith
      have h' := mul_le_mul_of_nonneg_right this hπ.le
      rw [sub_mul, div_mul_cancel₀ _ hπ.ne', one_mul] at h'
      exact h'
    have hAne : A ≠ 0 := hneg.ne
    set θ := ((m : ℝ) * π - κ) / A with hθ
    have hθ0 : 0 < θ := div_pos_of_neg_of_neg (by linarith) (by linarith)
    have hθπ : θ < π := by
      rw [hθ, div_lt_iff_of_neg (by linarith)]
      nlinarith
    have h := hpos θ hθ0 hθπ
    rw [show κ + A * θ = (m : ℝ) * π by rw [hθ]; field_simp; ring, Real.sin_int_mul_pi] at h
    exact lt_irrefl _ h
  · rw [hzero, abs_zero] at hA'
    linarith
  · have hA1 : 1 < A := by rwa [abs_of_pos hposA] at hA'
    set m : ℤ := ⌊κ / π⌋ + 1 with hm
    have hf1 := Int.floor_le (κ / π)
    have hf2 := Int.lt_floor_add_one (κ / π)
    have hm1 : κ < (m : ℝ) * π := by
      have : κ / π < (m : ℝ) := by rw [hm]; push_cast; linarith
      rwa [div_lt_iff₀ hπ] at this
    have hm2 : (m : ℝ) * π ≤ κ + π := by
      have : (m : ℝ) ≤ κ / π + 1 := by rw [hm]; push_cast; linarith
      have h' := mul_le_mul_of_nonneg_right this hπ.le
      rw [add_mul, div_mul_cancel₀ _ hπ.ne', one_mul] at h'
      exact h'
    have hAne : A ≠ 0 := hposA.ne'
    set θ := ((m : ℝ) * π - κ) / A with hθ
    have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
    have hθπ : θ < π := by
      rw [hθ, div_lt_iff₀ (by linarith)]
      nlinarith
    have h := hpos θ hθ0 hθπ
    rw [show κ + A * θ = (m : ℝ) * π by rw [hθ]; field_simp; ring, Real.sin_int_mul_pi] at h
    exact lt_irrefl _ h

/-- If `w ↦ K w` maps `ℍ` into `ℍ`, then `K` is a positive real. -/
lemma exists_pos_real_of_mul_into {K : ℂ} (h : ∀ w : ℂ, 0 < w.im → 0 < (K * w).im) :
    ∃ a : ℝ, 0 < a ∧ K = a := by
  have key : ∀ t : ℝ, 0 < K.re + t * K.im := by
    intro t
    have := h ((t : ℂ) + Complex.I) (by simp)
    simp at this
    linarith
  have hre : 0 < K.re := by simpa using key 0
  have him : K.im = 0 := by
    by_contra hne
    have := key (-(K.re + 1) / K.im)
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  exact ⟨K.re, hre, Complex.ext (by simp) (by simp [him])⟩

/-- If `w ↦ K / w` maps `ℍ` into `ℍ`, then `K` is a negative real. -/
lemma exists_neg_real_of_mul_inv_into {K : ℂ} (h : ∀ w : ℂ, 0 < w.im → 0 < (K * w⁻¹).im) :
    ∃ a : ℝ, a < 0 ∧ K = a := by
  have key : ∀ t : ℝ, 0 < t * K.im - K.re := by
    intro t
    set w : ℂ := (t : ℂ) + Complex.I with hw
    have hw0 : 0 < w.im := by simp [hw]
    have h1 := h w hw0
    have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr (fun h0 => by
      rw [h0] at hw0
      simp at hw0)
    have e : K * w⁻¹ = (((Complex.normSq w)⁻¹ : ℝ) : ℂ) * (K * (starRingEnd ℂ) w) := by
      rw [Complex.inv_def]
      ring
    rw [e, Complex.im_ofReal_mul] at h1
    have h2 : 0 < (K * (starRingEnd ℂ) w).im := by
      by_contra hle
      have := mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hns).le (not_lt.mp hle)
      linarith
    simp [hw] at h2
    linarith
  have hre : K.re < 0 := by linarith [key 0]
  have him : K.im = 0 := by
    by_contra hne
    have := key ((K.re - 1) / K.im)
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  exact ⟨K.re, hre, Complex.ext (by simp) (by simp [him])⟩

/-! ### The power family with `0 < |A| < 1` -/

section PowerSmall

variable {c : ℕ → ℂ} {c₀ A M₀ : ℝ} {K : ℂ}

/-- On the vertical line through `c₀`: `Im β(c₀ + i y) = y ^ A · Im (K e^{i A π/2})`. -/
lemma im_power_family_vertical {y : ℝ} (hy : 0 < y) :
    (K * (((c₀ : ℂ) + y * Complex.I) - c₀) ^ (A : ℂ) + M₀).im =
      y ^ A * (K * Complex.exp ((A * (π / 2) : ℝ) * Complex.I)).im := by
  rw [add_sub_cancel_left, ofReal_mul_I_cpow hy A, mul_left_comm, Complex.add_im,
    Complex.ofReal_im, add_zero, Complex.im_ofReal_mul]

/-- In the power family, `0 < A < 1` contradicts top injectivity. -/
theorem false_of_power_family_of_pos_of_lt_one (hc : IsJDominated c) (hA0 : 0 < A)
    (hA1 : A < 1)
    (hglob : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im ∧
      qSeriesExt c (K * (z - c₀) ^ (A : ℂ) + M₀) = qSeriesExt c z) : False := by
  set s₀ := (K * Complex.exp ((A * (π / 2) : ℝ) * Complex.I)).im with hs₀
  have hs₀pos : 0 < s₀ := im_mul_exp_pos_of_power_into (fun z hz => (hglob z hz).1)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hzy : ∀ y : ℝ, ((c₀ : ℂ) + y * Complex.I).im = y := by
    intro y
    simp
  have hrel : ∀ y : ℝ, max 1 topHeight ≤ y → topHeight ≤ y ^ A * s₀ → y ^ A * s₀ = y := by
    intro y hy htop
    have hy0 : 0 < y := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hy)
    obtain ⟨-, heq⟩ := hglob ((c₀ : ℂ) + y * Complex.I) (by rw [hzy]; exact hy0)
    obtain ⟨n, hn⟩ := exists_int_of_qSeriesExt_eq hc
      (by rw [im_power_family_vertical hy0]; exact htop)
      (by rw [hzy]; exact (le_max_right _ _).trans hy) heq
    have h := congrArg Complex.im hn
    rw [im_power_family_vertical hy0] at h
    have h2 : ((c₀ : ℂ) + y * Complex.I + n).im = y := by simp
    rw [h2] at h
    exact h
  have hq0 : 0 ≤ topHeight / s₀ := div_nonneg topHeight_pos.le hs₀pos.le
  set Y := max (max 1 topHeight) ((topHeight / s₀) ^ A⁻¹) with hY
  have hY1 : max 1 topHeight ≤ Y := le_max_left _ _
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hY1)
  have htopY : ∀ y : ℝ, Y ≤ y → topHeight ≤ y ^ A * s₀ := by
    intro y hy
    have h1 : (topHeight / s₀) ^ A⁻¹ ≤ y := (le_max_right _ _).trans hy
    have h2 : ((topHeight / s₀) ^ A⁻¹) ^ A ≤ y ^ A :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) h1 hA0.le
    rw [Real.rpow_inv_rpow hq0 hA0.ne', div_le_iff₀ hs₀pos] at h2
    exact h2
  have hs : ∀ y : ℝ, 0 < y → y ^ A * s₀ = y → s₀ = y ^ (1 - A) := by
    intro y hy h
    have hyA : 0 < y ^ A := Real.rpow_pos_of_pos hy A
    have h' : y ^ A * s₀ = y ^ A * y ^ (1 - A) := by
      rw [h, ← Real.rpow_add hy, show A + (1 - A) = (1 : ℝ) by ring, Real.rpow_one]
    exact mul_left_cancel₀ hyA.ne' h'
  have h1 := hs Y hY0 (hrel Y hY1 (htopY Y le_rfl))
  have h2 := hs (2 * Y) (by linarith)
    (hrel (2 * Y) (by linarith) (htopY (2 * Y) (by linarith)))
  have h3 : Y ^ (1 - A) < (2 * Y) ^ (1 - A) :=
    Real.rpow_lt_rpow hY0.le (by linarith) (by linarith)
  linarith

/-- Positivity of `sin (κ + A θ)` on `0 < θ < π` gives `sin κ ≥ 0` and `sin (κ + A π) ≥ 0`. -/
lemma sin_nonneg_endpoints {κ A : ℝ}
    (hpos : ∀ θ : ℝ, 0 < θ → θ < π → 0 < Real.sin (κ + A * θ)) :
    0 ≤ Real.sin κ ∧ 0 ≤ Real.sin (κ + A * π) := by
  have hπ := Real.pi_pos
  have hcont : Continuous fun θ : ℝ => Real.sin (κ + A * θ) := by fun_prop
  constructor
  · have ht : Tendsto (fun θ : ℝ => Real.sin (κ + A * θ)) (𝓝[>] 0) (𝓝 (Real.sin κ)) := by
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hπ] with θ hθ
    exact (hpos θ hθ.1 hθ.2).le
  · have ht : Tendsto (fun θ : ℝ => Real.sin (κ + A * θ)) (𝓝[<] π) (𝓝 (Real.sin (κ + A * π))) :=
      (hcont.tendsto π).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hπ] with θ hθ
    exact (hpos θ hθ.1 hθ.2).le

/-- For `−1 < A < 0`: on one of the vertical lines through `c₀ ± 1`, `β` converges to a point of
`ℍ` as the line approaches `ℝ`. -/
lemma exists_tendsto_power_family_of_neg (hA0 : A < 0) (hA1 : -1 < A) (hK : K ≠ 0)
    (hinto : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im) :
    ∃ (n : ℤ) (P : ℂ), 0 < P.im ∧
      Tendsto (fun s : ℝ => K * ((n : ℂ) + s * Complex.I) ^ (A : ℂ) + M₀) (𝓝[>] 0) (𝓝 P) := by
  have hπ := Real.pi_pos
  have hKn : 0 < ‖K‖ := norm_pos_iff.mpr hK
  set κ := Complex.arg K with hκ
  have hpos : ∀ θ : ℝ, 0 < θ → θ < π → 0 < Real.sin (κ + A * θ) := by
    intro θ hθ0 hθπ
    have h := im_mul_exp_pos_of_power_into hinto hθ0 hθπ
    rw [im_mul_exp_ofReal_mul_I] at h
    exact pos_of_mul_pos_right h hKn.le
  obtain ⟨hs0, hsπ⟩ := sin_nonneg_endpoints hpos
  have hcpow_cont : Continuous fun s : ℝ => ((1 : ℂ) + s * Complex.I) := by fun_prop
  by_cases hIm : 0 < K.im
  · -- the line through `c₀ + 1`
    refine ⟨1, K + M₀, by simpa using hIm, ?_⟩
    have h1 : Tendsto (fun s : ℝ => (1 : ℂ) + s * Complex.I) (𝓝[>] 0) (𝓝 1) := by
      have := (hcpow_cont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    have h2 : Tendsto (fun s : ℝ => ((1 : ℂ) + s * Complex.I) ^ (A : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have := (continuousAt_cpow_const (b := (A : ℂ)) Complex.one_mem_slitPlane).tendsto.comp h1
      simpa [Complex.one_cpow] using this
    have h3 := (h2.const_mul K).add_const (M₀ : ℂ)
    simpa using h3
  · -- the line through `c₀ − 1`
    have hKim : K.im = ‖K‖ * Real.sin κ := by
      have := im_mul_exp_ofReal_mul_I K 0
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, add_zero] at this
      exact this
    have hsκ : Real.sin κ = 0 := by
      have : ‖K‖ * Real.sin κ ≤ 0 := by rw [← hKim]; exact not_lt.mp hIm
      have : Real.sin κ ≤ 0 := nonpos_of_mul_nonpos_right this hKn
      linarith
    have hsπpos : 0 < Real.sin (κ + A * π) := by
      rcases hsπ.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsκ
        obtain ⟨m', hm'⟩ := Real.sin_eq_zero_iff.mp h.symm
        have hA : A = ((m' - m : ℤ) : ℝ) := by
          push_cast
          have : A * π = (m' - m) * π := by linarith
          exact mul_right_cancel₀ hπ.ne' this
        rw [hA] at hA0 hA1
        have h1 : m' - m < 0 := by exact_mod_cast hA0
        have h2 : -1 < m' - m := by exact_mod_cast hA1
        omega
    refine ⟨-1, K * Complex.exp ((A * π : ℝ) * Complex.I) + M₀, ?_, ?_⟩
    · rw [Complex.add_im, Complex.ofReal_im, add_zero, im_mul_exp_ofReal_mul_I]
      exact mul_pos hKn hsπpos
    · have hmap : Tendsto (fun s : ℝ => (-1 : ℂ) + s * Complex.I) (𝓝[>] 0)
          (𝓝[{z : ℂ | 0 ≤ z.im}] (-1)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc : Continuous fun s : ℝ => (-1 : ℂ) + s * Complex.I := by fun_prop
          have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          simpa using (le_of_lt (show (0 : ℝ) < s from hs))
      have hlog : Tendsto (fun s : ℝ => Complex.log ((-1 : ℂ) + s * Complex.I)) (𝓝[>] 0)
          (𝓝 (π * Complex.I)) := by
        have := (Complex.continuousWithinAt_log_of_re_neg_of_im_zero (z := -1) (by simp)
          (by simp)).tendsto.comp hmap
        rwa [Complex.log_neg_one] at this
      have hexp : Tendsto (fun s : ℝ => Complex.exp (Complex.log ((-1 : ℂ) + s * Complex.I) *
          A)) (𝓝[>] 0) (𝓝 (Complex.exp ((A * π : ℝ) * Complex.I))) := by
        have := (Complex.continuous_exp.tendsto _).comp (hlog.mul_const (A : ℂ))
        rw [show (π : ℂ) * Complex.I * A = ((A * π : ℝ) : ℂ) * Complex.I by push_cast; ring]
          at this
        exact this
      have hcp : Tendsto (fun s : ℝ => ((-1 : ℂ) + s * Complex.I) ^ (A : ℂ)) (𝓝[>] 0)
          (𝓝 (Complex.exp ((A * π : ℝ) * Complex.I))) := by
        refine hexp.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hne : (-1 : ℂ) + s * Complex.I ≠ 0 := by
          intro h0
          have h1 : ((-1 : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
          rw [h0, Complex.zero_im] at h1
          exact (ne_of_gt (show (0 : ℝ) < s from hs)) h1.symm
        rw [Complex.cpow_def_of_ne_zero hne]
      have h3 := (hcp.const_mul K).add_const (M₀ : ℂ)
      simpa using h3

/-- In the power family, `−1 < A < 0` contradicts periodicity. -/
theorem false_of_power_family_of_neg_of_gt_neg_one (hc : IsJDominated c) (hA0 : A < 0)
    (hA1 : -1 < A) (hK : K ≠ 0)
    (hglob : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im ∧
      qSeriesExt c (K * (z - c₀) ^ (A : ℂ) + M₀) = qSeriesExt c z) : False := by
  set s₀ := (K * Complex.exp ((A * (π / 2) : ℝ) * Complex.I)).im with hs₀
  have hs₀pos : 0 < s₀ := im_mul_exp_pos_of_power_into (fun z hz => (hglob z hz).1)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  obtain ⟨n, P, hP, hlim⟩ :=
    exists_tendsto_power_family_of_neg hA0 hA1 hK (fun z hz => (hglob z hz).1)
  have hgP : ContinuousAt (qSeriesExt c) P :=
    (differentiableOn_qSeriesExt hc).continuousOn.continuousAt
      (isOpen_upperHalfPlaneSet.mem_nhds hP)
  set C := ‖qSeriesExt c P‖ + 1 with hC
  have hev1 : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ‖qSeriesExt c (K * ((n : ℂ) + (s : ℂ) * Complex.I) ^ (A : ℂ) + M₀)‖ < C := by
    have := (continuous_norm.tendsto _).comp (hgP.tendsto.comp hlim)
    exact this.eventually (gt_mem_nhds (lt_add_one _))
  have hev2 : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), max 1 (C + jTail 1) / s₀ ≤ s ^ A :=
    (tendsto_rpow_neg_nhdsGT_zero hA0).eventually (eventually_ge_atTop _)
  obtain ⟨s, h1, h2, h3⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have hs : (0 : ℝ) < s := h3
  have hzs : 0 < ((c₀ : ℂ) + s * Complex.I).im := by simpa using hs
  have hzn : 0 < ((c₀ : ℂ) + s * Complex.I + n).im := by simpa using hs
  have heq := (hglob _ hzs).2
  have heqn := (hglob _ hzn).2
  rw [show (c₀ : ℂ) + s * Complex.I + n - c₀ = (n : ℂ) + s * Complex.I by ring,
    qSeriesExt_add_intCast c hzs n] at heqn
  have hmax : max 1 (C + jTail 1) ≤ s ^ A * s₀ := by
    rwa [div_le_iff₀ hs₀pos] at h2
  have hbig := lt_norm_qSeriesExt_of_le_im hc C
    (z := K * (((c₀ : ℂ) + s * Complex.I) - c₀) ^ (A : ℂ) + M₀)
    (by rw [im_power_family_vertical hs]; exact (le_max_left _ _).trans hmax)
    (by rw [im_power_family_vertical hs]; exact (le_max_right _ _).trans hmax)
  rw [heq, ← heqn] at hbig
  linarith

end PowerSmall

/-! ### The power family: conclusion -/

/-- **Power family.** A global symmetry `K (z − c₀)^A + M₀` (`A ≠ 0`, `K ≠ 0`) has `A = 1` and
`K > 0` real, or `A = −1` and `K < 0` real. -/
theorem power_family_cases {c : ℕ → ℂ} (hc : IsJDominated c) {c₀ A M₀ : ℝ} {K : ℂ}
    (hA : A ≠ 0) (hK : K ≠ 0)
    (hglob : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im ∧
      qSeriesExt c (K * (z - c₀) ^ (A : ℂ) + M₀) = qSeriesExt c z) :
    (A = 1 ∧ ∃ a : ℝ, 0 < a ∧ K = a) ∨ (A = -1 ∧ ∃ a : ℝ, a < 0 ∧ K = a) := by
  have hinto : ∀ z : ℂ, 0 < z.im → 0 < (K * (z - c₀) ^ (A : ℂ) + M₀).im :=
    fun z hz => (hglob z hz).1
  have hKn : 0 < ‖K‖ := norm_pos_iff.mpr hK
  have hpos : ∀ θ : ℝ, 0 < θ → θ < π → 0 < Real.sin (Complex.arg K + A * θ) := by
    intro θ hθ0 hθπ
    have h := im_mul_exp_pos_of_power_into hinto hθ0 hθπ
    rw [im_mul_exp_ofReal_mul_I] at h
    exact pos_of_mul_pos_right h hKn.le
  have habs := abs_le_one_of_sin_pos hpos
  have hshift : ∀ w : ℂ, 0 < w.im → 0 < ((c₀ : ℂ) + w).im := fun w hw => by simpa using hw
  rcases lt_trichotomy A 0 with hneg | hzero | hpos'
  · rcases (abs_le.mp habs).1.lt_or_eq with hgt | heq
    · exact (false_of_power_family_of_neg_of_gt_neg_one hc hneg hgt hK hglob).elim
    · right
      refine ⟨heq.symm, exists_neg_real_of_mul_inv_into fun w hw => ?_⟩
      have h := hinto _ (hshift w hw)
      rw [add_sub_cancel_left, ← heq, Complex.ofReal_neg, Complex.ofReal_one,
        Complex.cpow_neg_one, Complex.add_im, Complex.ofReal_im, add_zero] at h
      exact h
  · exact (hA hzero).elim
  · rcases (abs_le.mp habs).2.lt_or_eq with hlt | heq
    · exact (false_of_power_family_of_pos_of_lt_one hc hpos' hlt hglob).elim
    · left
      refine ⟨heq, exists_pos_real_of_mul_into fun w hw => ?_⟩
      have h := hinto _ (hshift w hw)
      rw [add_sub_cancel_left, heq, Complex.ofReal_one, Complex.cpow_one, Complex.add_im,
        Complex.ofReal_im, add_zero] at h
      exact h

end VOA.Moonshine.ConwayNorton
