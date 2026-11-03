/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.TraceNonvanish

/-!
# The leading `q`-coefficient is detected by the values on `ℍ`

Residual **(d)** (`FibreIndependent`) is proved by *peeling*: inside one `T`-eigenvalue fibre the
conformal weights differ by **integers**, so a vanishing linear combination of trace functions has a
well-defined lowest `q`-exponent, and the coefficient there is a linear combination of characters of
the *bottoms* — which `Modularity.CharIndependence.exists_trace_separating` separates.

The analytic input for that peeling is isolated here: a formal `q`-series with subexponential
coefficients whose `q`-evaluation vanishes on the imaginary axis has vanishing **leading**
coefficient.  The proof is elementary — evaluate at `τ = i·t`, where `q = e^{−2πt}` is a *positive
real* in `(0,1)` (`qParam_imAxis`), bound the tail geometrically, and let `t → ∞` by choosing `t`
explicitly.  No analytic continuation, no identity theorem, no Laurent expansion.

## Main results

* `tailBound` — the geometric tail estimate at radius `≤ 1/2`;
* `leading_coeff_eq_zero_of_qEvalAt_imAxis_eq_zero`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

/-- Every radius in `(0,1)` is `qParam` of a point of the imaginary axis. -/
theorem exists_imAxis_qParam {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (t : ℝ) (ht : 0 < t), qParam (imAxis t ht) = (ρ : ℂ) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  refine ⟨-Real.log ρ / (2 * Real.pi), div_pos (by linarith) hpi, ?_⟩
  rw [qParam_imAxis]
  congr 1
  rw [show -(2 * Real.pi * (-Real.log ρ / (2 * Real.pi))) = Real.log ρ from by
    field_simp]
  exact Real.exp_log hρ0

/-- **The leading coefficient is detected on the imaginary axis.**  If the `q`-evaluation of a
subexponential formal series vanishes at every point of `i·ℝ_{>0}`, its leading coefficient is `0`. -/
theorem leading_coeff_eq_zero_of_qEvalAt_imAxis_eq_zero (χ : FormalQSeries) (e₀ : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (e₀ + (n : ℂ))‖))
    (hzero : ∀ (t : ℝ) (ht : 0 < t), qEvalAt χ e₀ (imAxis t ht) = 0) :
    χ e₀ = 0 := by
  classical
  set a : ℕ → ℝ := fun n => ‖χ (e₀ + (n : ℂ))‖ with ha
  have hpos : ∀ n, 0 ≤ a n := fun n => norm_nonneg _
  -- the comparison constant, at radius `1/2`
  have hC : Summable (fun n : ℕ => a (n + 1) * (1 / 2 : ℝ) ^ n) := by
    have hsub' : Subexponential (fun n : ℕ => a (n + 1)) := by
      intro r hr
      obtain ⟨C, hCr⟩ := hsub r hr
      refine ⟨C * r, fun n => ?_⟩
      have h1 : a (n + 1) ≤ C * r ^ (n + 1) := hCr (n + 1)
      calc a (n + 1) ≤ C * r ^ (n + 1) := h1
        _ = C * r * r ^ n := by rw [pow_succ]; ring
    exact summable_of_subexponential (fun n => hpos (n + 1)) hsub' (by norm_num) (by norm_num)
  set C : ℝ := ∑' n : ℕ, a (n + 1) * (1 / 2 : ℝ) ^ n with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg (fun n => by positivity)
  -- the tail bound at every radius `ρ ≤ 1/2`
  have hbound : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → ‖χ e₀‖ ≤ ρ * C := by
    intro ρ hρ0 hρhalf
    have hρ1 : ρ < 1 := by linarith
    obtain ⟨t, ht, hq⟩ := exists_imAxis_qParam hρ0 hρ1
    have hz := hzero t ht
    rw [qEvalAt, hq] at hz
    have hz' : ∑' n : ℕ, χ (e₀ + (n : ℂ)) * (ρ : ℂ) ^ n = 0 := by
      rcases mul_eq_zero.mp hz with hex | hs
      · exact absurd hex (Complex.exp_ne_zero _)
      · exact hs
    -- summability of the complex series
    have hsummC : Summable (fun n : ℕ => χ (e₀ + (n : ℂ)) * (ρ : ℂ) ^ n) := by
      refine Summable.of_norm ?_
      have hnormeq : (fun n : ℕ => ‖χ (e₀ + (n : ℂ)) * (ρ : ℂ) ^ n‖)
          = fun n : ℕ => a n * ρ ^ n := by
        funext n
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      rw [hnormeq]
      exact summable_of_subexponential hpos hsub hρ0.le hρ1
    -- peel the `n = 0` term
    have hsplit := hsummC.tsum_eq_zero_add
    rw [hz'] at hsplit
    have h0 : χ (e₀ + ((0 : ℕ) : ℂ)) * (ρ : ℂ) ^ (0 : ℕ) = χ e₀ := by
      norm_num
    rw [h0] at hsplit
    have hchi : χ e₀ = -∑' n : ℕ, χ (e₀ + ((n + 1 : ℕ) : ℂ)) * (ρ : ℂ) ^ (n + 1) := by
      linear_combination -hsplit
    rw [hchi, norm_neg]
    -- bound the tail
    have htail : ‖∑' n : ℕ, χ (e₀ + ((n + 1 : ℕ) : ℂ)) * (ρ : ℂ) ^ (n + 1)‖
        ≤ ∑' n : ℕ, a (n + 1) * ρ ^ (n + 1) := by
      refine norm_tsum_le_tsum_norm ?_ |>.trans (le_of_eq ?_)
      · have hnormeq : (fun n : ℕ => ‖χ (e₀ + ((n + 1 : ℕ) : ℂ)) * (ρ : ℂ) ^ (n + 1)‖)
            = fun n : ℕ => a (n + 1) * ρ ^ (n + 1) := by
          funext n
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
        rw [hnormeq]
        have hsub' : Subexponential (fun n : ℕ => a (n + 1)) := by
          intro r hr
          obtain ⟨Cc, hCr⟩ := hsub r hr
          exact ⟨Cc * r, fun n => by
            have h1 : a (n + 1) ≤ Cc * r ^ (n + 1) := hCr (n + 1)
            calc a (n + 1) ≤ Cc * r ^ (n + 1) := h1
              _ = Cc * r * r ^ n := by rw [pow_succ]; ring⟩
        have := summable_of_subexponential (fun n => hpos (n + 1)) hsub' hρ0.le hρ1
        exact this.mul_right ρ |>.congr (fun n => by rw [pow_succ]; ring)
      · refine tsum_congr fun n => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    refine htail.trans ?_
    -- `∑ a(n+1) ρ^(n+1) = ρ * ∑ a(n+1) ρ^n ≤ ρ * C`
    have hmono : ∑' n : ℕ, a (n + 1) * ρ ^ (n + 1) ≤ ρ * C := by
      have heq : ∀ n : ℕ, a (n + 1) * ρ ^ (n + 1) = ρ * (a (n + 1) * ρ ^ n) := by
        intro n; rw [pow_succ]; ring
      have hsummρ : Summable (fun n : ℕ => a (n + 1) * ρ ^ n) := by
        have hsub' : Subexponential (fun n : ℕ => a (n + 1)) := by
          intro r hr
          obtain ⟨Cc, hCr⟩ := hsub r hr
          exact ⟨Cc * r, fun n => by
            have h1 : a (n + 1) ≤ Cc * r ^ (n + 1) := hCr (n + 1)
            calc a (n + 1) ≤ Cc * r ^ (n + 1) := h1
              _ = Cc * r * r ^ n := by rw [pow_succ]; ring⟩
        exact summable_of_subexponential (fun n => hpos (n + 1)) hsub' hρ0.le hρ1
      rw [tsum_congr heq, hsummρ.tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ hρ0.le
      refine Summable.tsum_mono hsummρ hC (fun n => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hpos (n + 1))
      exact pow_le_pow_left₀ hρ0.le hρhalf n
    exact hmono
  -- let `ρ → 0`
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ρ : ℝ := min (1 / 2) (ε / (C + 1)) with hρ
  have hCp : 0 < C + 1 := by linarith
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hρε : ρ ≤ ε / (C + 1) := min_le_right _ _
  calc ‖χ e₀‖ ≤ ρ * C := hbound ρ hρ0 hρhalf
    _ ≤ (ε / (C + 1)) * C := mul_le_mul_of_nonneg_right hρε hC0
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hCp]
        nlinarith
    _ = 0 + ε := (zero_add ε).symm

end VOA
