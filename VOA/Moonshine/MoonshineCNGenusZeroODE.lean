/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroPartner

/-!
# Genus zero on the abstract interface: the real linear ODE of an intertwined germ

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. Let `α` be holomorphic on an open
set `S` and satisfy `α (a n z + b n) = a′ n α(z) + b′ n` on `S` for real `a n → 1`, `b n → 0`,
`(a n, b n) ≠ (1, 0)` and real `a′ n, b′ n`. If `α` is not constant on `S` (two points with
different values), then `α` satisfies a first-order linear ODE with **real** coefficients:

`(λ z + μ) α′(z) = λ′ α(z) + μ′` on `S`, `(λ, μ) ≠ (0, 0)` (`exists_real_linear_ode`).

Proof: normalise `ε n = |a n − 1| + |b n|`, extract a subsequence along which
`((a n − 1)/ε n, b n/ε n) → (λ, μ)` (compactness; `|λ| + |μ| = 1`), differentiate
`(α (C n z) − α z)/ε n → (λ z + μ) α′(z)` (little-o form of the derivative), and read off the
right-hand side `((a′ n − 1)/ε n) α z + b′ n/ε n` at two points with different values: its
coefficients converge, and their limits are real because the coefficients are.

The construction of the intertwining sequence itself is the overlap construction
(`exists_intertwining_of_not_realAffine`).
-/

namespace VOA.Moonshine.ConwayNorton

open Filter Topology Set Asymptotics

/-- A convergent sequence of real numbers, read in `ℂ`, has a real limit. -/
lemma exists_real_of_tendsto_ofReal {r : ℕ → ℝ} {Λ : ℂ}
    (h : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 Λ)) :
    ∃ l : ℝ, Λ = l ∧ Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (l : ℂ)) := by
  have h1 : Tendsto r atTop (𝓝 Λ.re) := by
    have := (Complex.continuous_re.tendsto Λ).comp h
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (Λ.re : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h1
  exact ⟨Λ.re, tendsto_nhds_unique h h2, h2⟩

/-- **The real linear ODE**. -/
theorem exists_real_linear_ode {α : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S)
    (hα : DifferentiableOn ℂ α S) {a b a' b' : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1))
    (hb : Tendsto b atTop (𝓝 0)) (hne : ∀ n, a n ≠ 1 ∨ b n ≠ 0)
    (hrel : ∀ n, ∀ z ∈ S, α (affC (a n) (b n) z) = affC (a' n) (b' n) (α z))
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ S) (hz₂ : z₂ ∈ S) (h12 : α z₁ ≠ α z₂) :
    ∃ l m l' m' : ℝ, (l ≠ 0 ∨ m ≠ 0) ∧
      ∀ z ∈ S, ((l : ℂ) * z + m) * _root_.deriv α z = l' * α z + m' := by
  -- normalisation
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ε = fun n => |a n - 1| + |b n| := ⟨_, rfl⟩
  have hεn : ∀ n, ε n = |a n - 1| + |b n| := fun n => by rw [hε]
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    rw [hεn]
    rcases hne n with h | h
    · have h1 : 0 < |a n - 1| := abs_pos.mpr (sub_ne_zero.mpr h)
      have h2 := abs_nonneg (b n)
      linarith
    · have h1 : 0 < |b n| := abs_pos.mpr h
      have h2 := abs_nonneg (a n - 1)
      linarith
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun n => (a n - 1) / ε n := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, y = fun n => b n / ε n := ⟨_, rfl⟩
  have hxn : ∀ n, x n = (a n - 1) / ε n := fun n => by rw [hx]
  have hyn : ∀ n, y n = b n / ε n := fun n => by rw [hy]
  have hxy1 : ∀ n, |x n| + |y n| = 1 := by
    intro n
    rw [hxn, hyn, abs_div, abs_div, abs_of_pos (hεpos n), ← add_div, ← hεn,
      div_self (hεpos n).ne']
  have hxmem : ∀ n, x n ∈ Icc (-1 : ℝ) 1 := fun n =>
    abs_le.mp (by linarith [hxy1 n, abs_nonneg (y n)])
  have hymem : ∀ n, y n ∈ Icc (-1 : ℝ) 1 := fun n =>
    abs_le.mp (by linarith [hxy1 n, abs_nonneg (x n)])
  obtain ⟨L, -, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
    (x := fun n => ((x n, y n) : ℝ × ℝ)) (fun n => ⟨hxmem n, hymem n⟩)
  have hxl : Tendsto (fun n => x (φ n)) atTop (𝓝 L.1) := (continuous_fst.tendsto L).comp hlim
  have hym : Tendsto (fun n => y (φ n)) atTop (𝓝 L.2) := (continuous_snd.tendsto L).comp hlim
  have hlm : L.1 ≠ 0 ∨ L.2 ≠ 0 := by
    have h1 : Tendsto (fun n => |x (φ n)| + |y (φ n)|) atTop (𝓝 (|L.1| + |L.2|)) :=
      hxl.abs.add hym.abs
    have h2 : (fun n => |x (φ n)| + |y (φ n)|) = fun _ => (1 : ℝ) :=
      funext fun n => hxy1 (φ n)
    rw [h2] at h1
    have h3 : (1 : ℝ) = |L.1| + |L.2| := tendsto_nhds_unique tendsto_const_nhds h1
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    rw [hcon.1, hcon.2, abs_zero, add_zero] at h3
    exact one_ne_zero h3
  -- the difference quotients converge to `(λ z + μ) α′(z)`
  have hDlim : ∀ z ∈ S, Tendsto (fun n => (α (affC (a (φ n)) (b (φ n)) z) - α z) /
      (ε (φ n) : ℂ)) atTop (𝓝 (((L.1 : ℂ) * z + L.2) * _root_.deriv α z)) := by
    intro z hz
    have hd : HasDerivAt α (_root_.deriv α z) z :=
      ((hα z hz).differentiableAt (hSo.mem_nhds hz)).hasDerivAt
    obtain ⟨h, hh⟩ : ∃ h : ℕ → ℂ, h = fun n => affC (a n) (b n) z - z := ⟨_, rfl⟩
    have hhn : ∀ n, h n = ((a n - 1 : ℝ) : ℂ) * z + (b n : ℂ) := by
      intro n
      rw [hh]
      simp only [affC]
      push_cast
      ring
    have hh0 : Tendsto h atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ((a n - 1 : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto _).comp (ha.sub_const 1)
        rwa [sub_self, Complex.ofReal_zero] at this
      have h2 : Tendsto (fun n => (b n : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto _).comp hb
        rwa [Complex.ofReal_zero] at this
      have h3 := (h1.mul_const z).add h2
      rw [zero_mul, zero_add] at h3
      refine h3.congr fun n => ?_
      rw [hhn]
    have hho : Tendsto (fun n => h (φ n)) atTop (𝓝 0) := hh0.comp hφ.tendsto_atTop
    have hlo := (hasDerivAt_iff_isLittleO_nhds_zero.mp hd).comp_tendsto hho
    have hbig : (fun n => h (φ n)) =O[atTop] (fun n => (ε (φ n) : ℂ)) := by
      refine IsBigO.of_bound (‖z‖ + 1) (Eventually.of_forall fun n => ?_)
      rw [hhn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hεpos _), hεn]
      have h1 : ‖((a (φ n) - 1 : ℝ) : ℂ) * z + (b (φ n) : ℂ)‖ ≤
          |a (φ n) - 1| * ‖z‖ + |b (φ n)| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2 := abs_nonneg (a (φ n) - 1)
      have h3 := abs_nonneg (b (φ n))
      have h4 := norm_nonneg z
      nlinarith
    have hrem := (hlo.trans_isBigO hbig).tendsto_div_nhds_zero
    have hratio : Tendsto (fun n => h (φ n) / (ε (φ n) : ℂ)) atTop
        (𝓝 ((L.1 : ℂ) * z + L.2)) := by
      have h1 := (((Complex.continuous_ofReal.tendsto _).comp hxl).mul_const z).add
        ((Complex.continuous_ofReal.tendsto _).comp hym)
      refine h1.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [hhn, hxn, hyn]
      push_cast
      ring
    have hsum := hrem.add (hratio.mul_const (_root_.deriv α z))
    rw [zero_add] at hsum
    refine hsum.congr fun n => ?_
    have e1 : z + h (φ n) = affC (a (φ n)) (b (φ n)) z := by
      rw [hh]
      ring
    simp only [Function.comp_apply]
    rw [e1, smul_eq_mul]
    ring
  -- the right-hand side
  have hDrel : ∀ n, ∀ z ∈ S, (α (affC (a n) (b n) z) - α z) / (ε n : ℂ) =
      (((a' n - 1) / ε n : ℝ) : ℂ) * α z + ((b' n / ε n : ℝ) : ℂ) := by
    intro n z hz
    rw [hrel n z hz]
    simp only [affC]
    push_cast
    ring
  have hden : α z₁ - α z₂ ≠ 0 := sub_ne_zero.mpr h12
  have hA : Tendsto (fun n => (((a' (φ n) - 1) / ε (φ n) : ℝ) : ℂ)) atTop
      (𝓝 (((((L.1 : ℂ) * z₁ + L.2) * _root_.deriv α z₁) -
        (((L.1 : ℂ) * z₂ + L.2) * _root_.deriv α z₂)) / (α z₁ - α z₂))) := by
    have h := ((hDlim z₁ hz₁).sub (hDlim z₂ hz₂)).div_const (α z₁ - α z₂)
    refine h.congr fun n => ?_
    rw [hDrel _ z₁ hz₁, hDrel _ z₂ hz₂]
    rw [show (((a' (φ n) - 1) / ε (φ n) : ℝ) : ℂ) * α z₁ + ((b' (φ n) / ε (φ n) : ℝ) : ℂ) -
        ((((a' (φ n) - 1) / ε (φ n) : ℝ) : ℂ) * α z₂ + ((b' (φ n) / ε (φ n) : ℝ) : ℂ)) =
        (((a' (φ n) - 1) / ε (φ n) : ℝ) : ℂ) * (α z₁ - α z₂) by ring,
      mul_div_assoc, div_self hden, mul_one]
  obtain ⟨l', -, hA'⟩ := exists_real_of_tendsto_ofReal hA
  have hB : Tendsto (fun n => ((b' (φ n) / ε (φ n) : ℝ) : ℂ)) atTop
      (𝓝 (((L.1 : ℂ) * z₁ + L.2) * _root_.deriv α z₁ - l' * α z₁)) := by
    have h := (hDlim z₁ hz₁).sub (hA'.mul_const (α z₁))
    refine h.congr fun n => ?_
    rw [hDrel _ z₁ hz₁]
    ring
  obtain ⟨m', -, hB'⟩ := exists_real_of_tendsto_ofReal hB
  refine ⟨L.1, L.2, l', m', hlm, fun z hz => ?_⟩
  have h2 : Tendsto (fun n => (α (affC (a (φ n)) (b (φ n)) z) - α z) / (ε (φ n) : ℂ)) atTop
      (𝓝 ((l' : ℂ) * α z + m')) := by
    have h := (hA'.mul_const (α z)).add hB'
    refine h.congr fun n => ?_
    rw [hDrel _ z hz]
  exact tendsto_nhds_unique (hDlim z hz) h2

end VOA.Moonshine.ConwayNorton
