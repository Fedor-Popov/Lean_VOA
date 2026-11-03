/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QEvalHolomorphic

/-!
# The convolution ↔ product bridge

Zhu's block conditions (`Modularity.ZhuBlockConditions.IsFormalBlock`) are stated with the formal
convolution `qConv f χ e = Σᶠ n, f n · χ(e − n)` — that is what the recursion produces.  To read
them analytically one needs `qConv` to become **multiplication of functions on `ℍ`**:

  `qEvalC_qConv : qEvalC (qConv f χ) h z = (Σ' n, f n · qⁿ) · qEvalC χ h z`.

Together with `Modularity.QEvalHolomorphic.deriv_qEvalC` (`qDeriv ↦ (2πi)⁻¹ d/dz`) this is the
complete dictionary turning Zhu's three *formal* block conditions into honest identities between
holomorphic functions on the upper half-plane.

## Hypotheses

* `χ` is supported on `h + ℕ` (`hsupp`) — automatic for the one-point functions of a module with
  a conformal weight, since the weight spaces below `h` vanish;
* both `Σ ‖f n qⁿ‖` and `Σ ‖χ(h+n) qⁿ‖` converge — the growth datum of `Modularity.GrowthBound`
  gives the second, and the first holds for the Eisenstein family `zhuG k`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex

/-- Under the support hypothesis, the convolution at `h + m` is a **finite** sum. -/
theorem qConv_apply_of_support (f : ℕ → ℂ) (χ : FormalQSeries) (h : ℂ)
    (hsupp : ∀ i : ℤ, i < 0 → χ (h + (i : ℂ)) = 0) (m : ℕ) :
    qConv f χ (h + (m : ℂ))
      = ∑ n ∈ Finset.range (m + 1), f n * χ (h + ((m - n : ℕ) : ℂ)) := by
  classical
  have hzero : ∀ n : ℕ, n ∉ Finset.range (m + 1) → f n * χ (h + (m : ℂ) - (n : ℂ)) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hlt : ((m : ℤ) - (n : ℤ)) < 0 := by omega
    have hcast : h + (m : ℂ) - (n : ℂ) = h + (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    rw [hcast, hsupp _ hlt, mul_zero]
  have hsub : (Function.support fun n : ℕ => f n * χ (h + (m : ℂ) - (n : ℂ)))
      ⊆ (Finset.range (m + 1) : Finset ℕ) := by
    intro n hn
    by_contra hc
    exact hn (hzero n hc)
  rw [qConv, finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_range] at hn
  congr 2
  have : (n : ℤ) ≤ (m : ℤ) := by omega
  push_cast [Nat.cast_sub (by omega : n ≤ m)]
  ring

/-- **Convolution becomes multiplication.** -/
theorem qEvalC_qConv (f : ℕ → ℂ) (χ : FormalQSeries) (h : ℂ) {z : ℂ}
    (hsupp : ∀ i : ℤ, i < 0 → χ (h + (i : ℂ)) = 0)
    (hf : Summable fun n : ℕ => ‖f n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖)
    (hχ : Summable fun n : ℕ =>
      ‖χ (h + (n : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖) :
    qEvalC (qConv f χ) h z
      = (∑' n : ℕ, f n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z))
          * qEvalC χ h z := by
  classical
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hχ
  have hterm : ∀ m : ℕ, (qConv f χ) (h + (m : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * z)
      = ∑ n ∈ Finset.range (m + 1),
          (f n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z))
            * (χ (h + ((m - n : ℕ) : ℂ))
              * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m - n : ℕ) : ℕ) : ℂ) * z)) := by
    intro m
    rw [qConv_apply_of_support f χ h hsupp m, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_range] at hn
    have hle : n ≤ m := by omega
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m - n : ℕ) : ℕ) : ℂ) * z)
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * z) := by
      rw [← Complex.exp_add]
      congr 1
      have hc : ((m - n : ℕ) : ℂ) = (m : ℂ) - (n : ℂ) := by
        push_cast [Nat.cast_sub hle]; ring
      rw [hc]; ring
    rw [← hexp]
    ring
  rw [qEvalC, qEvalC, qSeriesC, qSeriesC]
  simp only [qTerm]
  rw [tsum_congr hterm, ← hcauchy]
  ring

end VOA
