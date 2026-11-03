/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# An explicit form of "the exponential beats every polynomial"

`Real.exp_neg_le_factorial_div_pow` bounds `exp (-x)` by `k!/xᵏ` for every `k`, from a single
term of the exponential series.  It is the asymptotics-free input behind every Gaussian decay
estimate in this development, and it imports nothing.
-/

namespace Real

/-- `exp (-x) ≤ k! / xᵏ` for `x > 0`: the `k`-th term of the exponential series bounds `exp`
from below. -/
theorem exp_neg_le_factorial_div_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (k.factorial : ℝ) / x ^ k := by
  have hle : x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx.le (k + 1))
    exact Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ k)
  have hpos : (0 : ℝ) < x ^ k / (k.factorial : ℝ) := by positivity
  rw [Real.exp_neg]
  have hinv := inv_anti₀ hpos hle
  rwa [inv_div] at hinv

end Real
