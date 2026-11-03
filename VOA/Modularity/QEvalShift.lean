/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LeadingCoeff

/-!
# Rebasing a `q`-evaluation across a vanishing initial segment

The fourth brick of residual **(d)**.  In the peeling argument the members of one `T`-eigenvalue
fibre have conformal weights differing by **integers** (`tEigen_eq_iff`), so their trace functions
are `q`-series based at *different* points of a single `ℤ`-coset.  To compare them they must all be
rebased to the *lowest* one — which is legitimate exactly because the coefficients below a module's
own conformal weight vanish (`OnePointSupported`).

  `qEvalAt χ d τ = qEvalAt χ (d + k) τ`   whenever `χ (d + s) = 0` for all `s < k`.

## Main results

* `exp_qParam_pow` — `e^{2πiτk} = q^k`;
* `qEvalAt_shift`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

theorem exp_qParam_pow (τ : UpperHalfPlane) (k : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (k : ℂ)) = (qParam τ) ^ k := by
  rw [qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Rebasing.**  If the coefficients of `χ` vanish on the initial segment `d, …, d+k−1`, the
`q`-evaluation may be based at `d + k` instead of `d`. -/
theorem qEvalAt_shift (χ : FormalQSeries) (d : ℂ) (k : ℕ) (τ : UpperHalfPlane)
    (hsum : QSummableAt χ d τ) (hvan : ∀ s : ℕ, s < k → χ (d + (s : ℂ)) = 0) :
    qEvalAt χ d τ = qEvalAt χ (d + (k : ℂ)) τ := by
  classical
  have hshift : Summable (fun n : ℕ => χ (d + ((n + k : ℕ) : ℂ)) * (qParam τ) ^ (n + k)) :=
    (summable_nat_add_iff k).2 hsum
  have hzero : ∑ i ∈ Finset.range k, χ (d + (i : ℂ)) * (qParam τ) ^ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hvan i (Finset.mem_range.mp hi), zero_mul]
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => χ (d + (n : ℂ))
    * (qParam τ) ^ n) k hsum
  rw [hzero, zero_add] at hsplit
  -- reindex the tail
  have hterm : ∀ n : ℕ, χ (d + ((n + k : ℕ) : ℂ)) * (qParam τ) ^ (n + k)
      = (χ ((d + (k : ℂ)) + (n : ℂ)) * (qParam τ) ^ n) * (qParam τ) ^ k := by
    intro n
    have hc : d + ((n + k : ℕ) : ℂ) = (d + (k : ℂ)) + (n : ℂ) := by push_cast; ring
    rw [hc, pow_add]
    ring
  have htail : ∑' n : ℕ, χ (d + ((n + k : ℕ) : ℂ)) * (qParam τ) ^ (n + k)
      = (∑' n : ℕ, χ ((d + (k : ℂ)) + (n : ℂ)) * (qParam τ) ^ n) * (qParam τ) ^ k := by
    rw [tsum_congr hterm]
    exact tsum_mul_right
  rw [qEvalAt, qEvalAt, ← hsplit, htail]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (d + (k : ℂ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * d) * (qParam τ) ^ k := by
    rw [mul_add, Complex.exp_add, exp_qParam_pow]
  rw [hexp]
  ring

end VOA
