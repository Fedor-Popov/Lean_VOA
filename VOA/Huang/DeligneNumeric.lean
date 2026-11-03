/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Deligne's theorem — realness and integrality of dimensions

Two elementary facts that turn the categorical positivity of a symmetric fusion category into
`d ∈ ℤ_{>0}` (EGNO §9.9; Deligne, *Catégories tensorielles* §1):

* `im_eq_zero_of_pow_re_pos` — if `re (z ^ n) > 0` for every `n ≥ 1`, then `z` is a positive real.
  (Apply to `z = symDim X`: `X^{⊗n}` is a nonzero object, so its braided dimension `d^n` has positive
  real part.)
* `exists_nat_of_descPochhammer_nonneg` — if `d` is real and `d(d-1)⋯(d-k+1) ≥ 0` for all `k`,
  then `d ∈ ℕ`.  (Apply with `k! · dim Λ^k X = d(d-1)⋯(d-k+1)`: an exterior power is either zero
  or has positive dimension.)

No `sorry`, no new axioms.
-/

noncomputable section

namespace VOA.Huang.Deligne

open Complex Real Polynomial

/-- A real angle `0 < |θ| ≤ π` has a positive multiple `nθ` with `cos (nθ) ≤ 0`. -/
theorem exists_cos_nonpos {θ : ℝ} (h0 : θ ≠ 0) (hpi : |θ| ≤ π) :
    ∃ n : ℕ, 0 < n ∧ Real.cos (n * θ) ≤ 0 := by
  have ha : 0 < |θ| := abs_pos.mpr h0
  -- `n = ⌈(π/2)/|θ|⌉`
  set n : ℕ := ⌈(π / 2) / |θ|⌉₊ with hn
  have hpos : 0 < (π / 2) / |θ| := div_pos (by positivity) ha
  have hn1 : 0 < n := Nat.ceil_pos.mpr hpos
  have hge : (π / 2) / |θ| ≤ n := Nat.le_ceil _
  have hlt : (n : ℝ) < (π / 2) / |θ| + 1 := Nat.ceil_lt_add_one hpos.le
  have h1 : π / 2 ≤ n * |θ| := by
    rw [div_le_iff₀ ha] at hge; linarith
  have h2 : n * |θ| < π / 2 + |θ| := by
    have := mul_lt_mul_of_pos_right hlt ha
    rw [add_mul, div_mul_cancel₀ _ ha.ne', one_mul] at this
    exact this
  refine ⟨n, hn1, ?_⟩
  have hc : Real.cos (n * |θ|) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
  rcases abs_choice θ with h | h
  · rwa [h] at hc
  · rw [h, mul_neg, Real.cos_neg] at hc; exact hc

/-- If every positive power of `z` has positive real part, `z` is a positive real. -/
theorem im_eq_zero_of_pow_re_pos {z : ℂ} (h : ∀ n : ℕ, 0 < n → 0 < (z ^ n).re) :
    z.im = 0 ∧ 0 < z.re := by
  have hre : 0 < z.re := by simpa using h 1 one_pos
  have hz : z ≠ 0 := by rintro rfl; simp at hre
  by_contra hcon
  have him : z.im ≠ 0 := fun h' => hcon ⟨h', hre⟩
  have harg : z.arg ≠ 0 := by
    intro ha
    rw [Complex.arg_eq_zero_iff] at ha
    exact him (by
      have := ha.2
      exact this)
  obtain ⟨n, hn, hc⟩ := exists_cos_nonpos harg (abs_arg_le_pi z)
  have hpow : z ^ n = ((‖z‖ ^ n : ℝ) : ℂ) * Complex.exp (((n * z.arg : ℝ) : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hre_n : (z ^ n).re = ‖z‖ ^ n * Real.cos (n * z.arg) := by
    rw [hpow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have := h n hn
  rw [hre_n] at this
  have hp : 0 < ‖z‖ ^ n := pow_pos (norm_pos_iff.mpr hz) n
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hp.le hc]

/-- A real number `d` all of whose falling factorials `d(d-1)⋯(d-k+1)` are nonnegative is a
natural number. -/
theorem exists_nat_of_descPochhammer_nonneg {d : ℝ}
    (h : ∀ k : ℕ, 0 ≤ (descPochhammer ℝ k).eval d) : ∃ n : ℕ, d = n := by
  have hd : 0 ≤ d := by simpa using h 1
  by_contra hcon
  push Not at hcon
  set m : ℕ := ⌊d⌋₊
  have hm : (m : ℝ) < d := lt_of_le_of_ne (Nat.floor_le hd) (fun e => hcon m e.symm)
  have hm1 : d < m + 1 := Nat.lt_floor_add_one d
  have hpos : 0 < (descPochhammer ℝ (m + 1)).eval d :=
    descPochhammer_pos (by push_cast; simpa using hm)
  have := h (m + 2)
  rw [descPochhammer_succ_eval] at this
  have hneg : d - ((m + 1 : ℕ) : ℝ) < 0 := by push_cast; linarith
  nlinarith

end VOA.Huang.Deligne
