/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Müger's criterion on finite data

The first step of Gannon–Rayhaun Proposition 2.17 (`ITannakian`): in a pseudo-unitary
premodular category, the trace of the double braiding of two simples is given by the
**balancing formula**

  `S̃_ab = ∑_c N_ab^c (θ_c / (θ_a θ_b)) d_c`,

while `d_a d_b = ∑_c N_ab^c d_c`.  With `d_c > 0` and `|θ_c| = 1`, the triangle inequality shows

  `balancedS_eq_iff : S̃_ab = d_a d_b  ⟺  θ_c = θ_a θ_b for every c with N_ab^c ≠ 0`

(`muger_numeric`).  In particular, for two labels of trivial twist (integer conformal weight),
`S_ab = S₀₀ d_a d_b` forces every fusion channel `c` of `a ⊗ b` to have trivial twist
(`twist_eq_one_of_factorized`): the integer-weight labels are closed under fusion.  The categorical
half (the double braiding itself is the identity) is in `Huang/TannakianCategory.lean`.

This file is pure algebra over `ℂ`; nothing is assumed.
-/

noncomputable section

namespace VOA.Huang.Tannakian

open Complex Finset

variable {ι : Type*} [Fintype ι]

/-- The **balancing formula** for the trace of the double braiding on `X_a ⊗ X_b`:
`S̃_ab = ∑_c N_ab^c (θ_c / (θ_a θ_b)) d_c`. -/
def balancedS (N : ι → ι → ι → ℕ) (θ : ι → ℂ) (d : ι → ℝ) (a b : ι) : ℂ :=
  ∑ c, (N a b c : ℂ) * (θ c / (θ a * θ b)) * (d c : ℂ)

/-- An elementary lemma: a nonnegatively weighted sum of unit complex numbers equals the total
weight only if every number with positive weight is `1`. -/
theorem eq_one_of_sum_weighted_eq {w : ι → ℝ} {z : ι → ℂ} (hw : ∀ c, 0 ≤ w c)
    (hz : ∀ c, ‖z c‖ = 1) (hsum : ∑ c, (w c : ℂ) * z c = ∑ c, (w c : ℂ)) :
    ∀ c, w c ≠ 0 → z c = 1 := by
  -- real parts: `∑ w (1 - Re z) = 0`, a sum of nonnegative terms
  have hre : ∑ c, w c * (1 - (z c).re) = 0 := by
    have h := congrArg Complex.re hsum
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h, sub_self]
  have hle : ∀ c, (z c).re ≤ 1 := fun c => (Complex.re_le_norm (z c)).trans (hz c).le
  have hnn : ∀ c ∈ (univ : Finset ι), 0 ≤ w c * (1 - (z c).re) :=
    fun c _ => mul_nonneg (hw c) (sub_nonneg.mpr (hle c))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hre
  intro c hc
  have h1 : (z c).re = 1 := by
    have := hzero c (mem_univ c)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · linarith
  -- `|z| = 1` and `Re z = 1` force `Im z = 0`
  have hn := hz c
  rw [Complex.norm_eq_sqrt_sq_add_sq, h1, Real.sqrt_eq_one] at hn
  have him : (z c).im = 0 := by nlinarith [sq_nonneg (z c).im]
  exact Complex.ext h1 (by simpa using him)

variable (N : ι → ι → ι → ℕ) (θ : ι → ℂ) (d : ι → ℝ)

/-- The easy direction of Müger's criterion: if every fusion channel `c` of `a ⊗ b` has
`θ_c = θ_a θ_b`, the balanced `S̃_ab` is `∑_c N_ab^c d_c`. -/
theorem balancedS_eq_of_twist (a b : ι) (hθa : θ a ≠ 0) (hθb : θ b ≠ 0)
    (h : ∀ c, N a b c ≠ 0 → θ c = θ a * θ b) :
    balancedS N θ d a b = ∑ c, (N a b c : ℂ) * (d c : ℂ) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : N a b c = 0
  · simp [hc]
  · rw [h c hc, div_self (mul_ne_zero hθa hθb), mul_one]

/-- **Müger's criterion, numerical form (pseudo-unitary).** If all `d_c > 0`, all `|θ_c| = 1`,
and `d_a d_b = ∑_c N_ab^c d_c`, then `S̃_ab = d_a d_b` **iff** every fusion channel `c` of
`a ⊗ b` has `θ_c = θ_a θ_b`. -/
theorem muger_numeric (hd : ∀ c, 0 < d c) (hθ : ∀ c, ‖θ c‖ = 1) (a b : ι)
    (hmul : (d a : ℂ) * (d b : ℂ) = ∑ c, (N a b c : ℂ) * (d c : ℂ)) :
    balancedS N θ d a b = (d a : ℂ) * (d b : ℂ) ↔ ∀ c, N a b c ≠ 0 → θ c = θ a * θ b := by
  have hne : ∀ c, θ c ≠ 0 := fun c h => by have := hθ c; rw [h, norm_zero] at this; simp at this
  constructor
  · intro hS c hc
    have key := eq_one_of_sum_weighted_eq (w := fun c => (N a b c : ℝ) * d c)
      (z := fun c => θ c / (θ a * θ b))
      (fun c => mul_nonneg (Nat.cast_nonneg _) (hd c).le)
      (fun c => by rw [norm_div, norm_mul, hθ, hθ, hθ]; norm_num)
      (by
        have e1 : ∑ c, (((N a b c : ℝ) * d c : ℝ) : ℂ) = ∑ c, (N a b c : ℂ) * (d c : ℂ) :=
          Finset.sum_congr rfl fun c _ => by push_cast; ring
        simp only
        rw [e1, ← hmul, ← hS, balancedS]
        refine Finset.sum_congr rfl fun c _ => ?_
        push_cast; ring)
      c (mul_ne_zero (Nat.cast_ne_zero.mpr hc) (hd c).ne')
    rwa [div_eq_one_iff_eq (mul_ne_zero (hne a) (hne b))] at key
  · intro h
    rw [balancedS_eq_of_twist N θ d a b (hne a) (hne b) h, hmul]

/-- **Integer-weight labels are closed under fusion** (the label part of GR Prop. 2.17): if
`θ_a = θ_b = 1` and `S̃_ab = d_a d_b`, every fusion channel of `a ⊗ b` has `θ_c = 1`. -/
theorem twist_eq_one_of_factorized (hd : ∀ c, 0 < d c) (hθ : ∀ c, ‖θ c‖ = 1) {a b : ι}
    (ha : θ a = 1) (hb : θ b = 1)
    (hmul : (d a : ℂ) * (d b : ℂ) = ∑ c, (N a b c : ℂ) * (d c : ℂ))
    (hS : balancedS N θ d a b = (d a : ℂ) * (d b : ℂ)) :
    ∀ c, N a b c ≠ 0 → θ c = 1 := by
  intro c hc
  rw [(muger_numeric N θ d hd hθ a b hmul).mp hS c hc, ha, hb, one_mul]

/-- The same, with the normalized `S`-matrix `S_ab = S₀₀ · S̃_ab` (either orientation of complex
conjugation, since `d_a d_b` is real): the `ITannakian` hypothesis `S_ab = S₀₀ d_a d_b` is exactly
`S̃_ab = d_a d_b`. -/
theorem balancedS_eq_iff_factorized {S00 : ℝ} (hS00 : S00 ≠ 0) (a b : ι) (Sab : ℂ)
    (hSab : Sab = (S00 : ℂ) * balancedS N θ d a b ∨
      Sab = (S00 : ℂ) * star (balancedS N θ d a b)) :
    Sab = (S00 : ℂ) * (d a : ℂ) * (d b : ℂ) ↔ balancedS N θ d a b = (d a : ℂ) * (d b : ℂ) := by
  have h0 : (S00 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS00
  have hreal : star ((d a : ℂ) * (d b : ℂ)) = (d a : ℂ) * (d b : ℂ) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  rcases hSab with h | h <;> rw [h, mul_assoc]
  · exact ⟨fun h' => mul_left_cancel₀ h0 h', fun h' => by rw [h']⟩
  · constructor
    · intro h'
      have := mul_left_cancel₀ h0 h'
      rw [← hreal, ← this, star_star]
    · intro h'; rw [h', hreal]

end VOA.Huang.Tannakian
