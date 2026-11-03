/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingResidue

/-!
# `ZhuUCore.u_core` — the associator's `u`-family scalar Vandermonde–Chu identity (Zhu Thm 2.1.2)

## Status
`sorry`-free, with no project axioms. **`u_core`** (with `cbz_upper_neg`, `trinomB`,
`inner_collapse`) is an *unconditional* combinatorial identity, consumed by the proved
`VOA.associator_core` and hence by the unconditional `Ring (A 𝒱)` (`ZhuRingInstance`).
`#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Finset VOA
open VOA.ZhuRes

namespace ZhuUCore

/-! ## Upper negation: `(-1)^i · C(m+i, i) = C(-m-1, i)`. -/

/-- Upper negation for the generalized binomial: `C(-m-1, i) = (-1)^i · C(m+i, i)`
(equivalently `(-1)^i · gBinom (m+i) i = cbz (-m-1) i`). -/
theorem cbz_upper_neg (m : ℤ) (i : ℕ) :
    cbz (-m - 1) (i : ℤ) = (-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i := by
  -- `C(-m-1, i) = (-1)^i C(m+i, i)`.  Clear the factorial and compare falling products.
  rw [cbz_apply_nonneg (-m - 1) (by positivity), show ((i : ℤ)).toNat = i from by simp]
  have hfac : ((i.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  refine mul_left_cancel₀ hfac ?_
  rw [gBinom_mul_factorial (-m - 1) i,
    show ((i.factorial : ℕ) : ℂ) * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i)
        = (-1 : ℂ) ^ i * (((i.factorial : ℕ) : ℂ) * gBinom (m + (i : ℤ)) i) from by ring,
    gBinom_mul_factorial (m + (i : ℤ)) i]
  -- `∏_{r<i}((-m-1)-r) = (-1)^i ∏_{r<i}((m+i)-r)`.
  -- Pull `(-1)` out of each LHS factor, then reflect the index.
  have hneg : (∏ r ∈ Finset.range i, (((-m - 1 : ℤ) : ℂ) - (r : ℂ)))
      = (-1 : ℂ) ^ i * ∏ r ∈ Finset.range i, ((m : ℂ) + 1 + (r : ℂ)) := by
    rw [show (-1 : ℂ) ^ i = ∏ _r ∈ Finset.range i, (-1 : ℂ) from by
        rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun r _ => by push_cast; ring)
  have hrefl : (∏ r ∈ Finset.range i, ((m : ℂ) + 1 + (r : ℂ)))
      = ∏ r ∈ Finset.range i, ((((m : ℤ) + (i : ℤ) : ℤ) : ℂ) - (r : ℂ)) := by
    rw [← Finset.prod_range_reflect (fun r => (((m : ℤ) + (i : ℤ) : ℤ) : ℂ) - (r : ℂ)) i]
    refine Finset.prod_congr rfl (fun r hr => ?_)
    have hri : r < i := Finset.mem_range.mp hr
    push_cast
    rw [show ((i - 1 - r : ℕ) : ℂ) = (i : ℂ) - 1 - (r : ℂ) from by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
    ring
  rw [hneg, hrefl]

/-! ## Trinomial revision in the `(a+b, b)` form: `C(K,a)·C(K-a,b) = C(K,a+b)·C(a+b,b)`. -/

/-- Trinomial revision (`K : ℕ`, `a b : ℤ`): `C(K,a)·C(K-a,b) = C(K,a+b)·C(a+b,b)`.
Same shape as `ZhuRes.stepB` but with the kept upper index `a+b` and lower index `b`. -/
theorem trinomB (K : ℕ) (a b : ℤ) :
    cbz (K : ℤ) a * cbz ((K : ℤ) - a) b = cbz (K : ℤ) (a + b) * cbz (a + b) b := by
  rcases lt_or_ge a 0 with ha | ha
  · -- `a < 0`: `cbz K a = 0`; on the RHS the upper index `a+b` ... handle by sub-cases.
    rw [cbz_apply_neg (K : ℤ) ha, zero_mul]
    rcases lt_or_ge b 0 with hb | hb
    · rw [cbz_apply_neg (a + b) (by omega), mul_zero]
    rcases lt_or_ge (a + b) 0 with hab | hab
    · rw [cbz_apply_neg (K : ℤ) hab, zero_mul]
    · rw [cbz_lt hab (by omega : a + b < b), mul_zero]
  rcases lt_or_ge b 0 with hb | hb
  · -- `b < 0`: `cbz (K-a) b = 0` and `cbz (a+b) b = 0`.
    rw [cbz_apply_neg ((K : ℤ) - a) hb, cbz_apply_neg (a + b) hb, mul_zero, mul_zero]
  -- `0 ≤ a, 0 ≤ b`, so `0 ≤ a + b`.
  rcases lt_or_ge (K : ℤ) (a + b) with hKab | hKab
  · -- `a+b > K`: RHS `cbz K (a+b) = 0`; LHS also 0 (`cbz K a` or `cbz (K-a) b` vanishes).
    rw [cbz_lt (by positivity) hKab, zero_mul]
    rcases lt_or_ge (K : ℤ) a with hKa | hKa
    · rw [cbz_lt (by positivity) hKa, zero_mul]
    · rw [cbz_lt (by omega : 0 ≤ (K : ℤ) - a) (by omega : (K : ℤ) - a < b), mul_zero]
  -- `0 ≤ a, 0 ≤ b, a+b ≤ K`: reduce all to `Nat.choose`.
  obtain ⟨A, rfl⟩ : ∃ A : ℕ, a = (A : ℤ) := ⟨a.toNat, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B : ℕ, b = (B : ℤ) := ⟨b.toNat, by omega⟩
  have hABK : A + B ≤ K := by exact_mod_cast hKab
  have hAK : A ≤ K := by omega
  rw [show ((K : ℤ) - (A : ℤ)) = ((K - A : ℕ) : ℤ) from by rw [Nat.cast_sub hAK],
      show ((A : ℤ) + (B : ℤ)) = ((A + B : ℕ) : ℤ) from by push_cast; ring,
      cbz_natCast_eq_choose hAK,
      cbz_natCast_eq_choose (by omega : B ≤ K - A),
      cbz_natCast_eq_choose hABK,
      cbz_natCast_eq_choose (by omega : B ≤ A + B),
      ← Nat.cast_mul, ← Nat.cast_mul]
  -- `K.choose A * (K-A).choose B = K.choose (A+B) * (A+B).choose B`.
  congr 1
  have hcm := Nat.choose_mul (n := K) (k := A + B) (s := A) (by omega)
  rw [Nat.add_sub_cancel_left] at hcm
  -- `hcm : K.choose (A+B) * (A+B).choose A = K.choose A * (K-A).choose B`.
  rw [← hcm, ← Nat.choose_symm (by omega : A ≤ A + B), show (A + B) - A = B from by omega]

/-! ## The inner sub-identity (via trinomial revision + Vandermonde, for `t ≤ β+1`). -/

/-- For `t ≤ β+1`:  the inner `i`-sum collapses to a single `cbz`:
`∑_i C(-m-1,i)·C(K, m+1+i)·C(K-m-1-i, β+1-i-t) = C(K, m+β+2-t)`. -/
theorem inner_collapse (K β : ℕ) (m : ℤ) (t : ℕ) (ht : t ≤ β + 1) :
    ∑ i ∈ Finset.range (β + 2),
        cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
          * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
      = cbz (K : ℤ) (m + (β : ℤ) + 2 - (t : ℤ)) := by
  -- Trinomial revision: `C(K, m+1+i)·C(K-(m+1+i), β+1-i-t) = C(K, m+β+2-t)·C(m+β+2-t, β+1-i-t)`.
  -- The kept upper index `a+b = (m+1+i)+(β+1-i-t) = m+β+2-t` is independent of `i`.
  rw [show ∑ i ∈ Finset.range (β + 2),
          cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
        = cbz (K : ℤ) (m + (β : ℤ) + 2 - (t : ℤ))
            * ∑ i ∈ Finset.range (β + 2),
                cbz (-m - 1) (i : ℤ)
                  * cbz (m + (β : ℤ) + 2 - (t : ℤ)) (((β : ℤ) + 1 - (t : ℤ)) - (i : ℤ)) from ?_]
  · -- Vandermonde: `∑_i C(-m-1, i)·C(m+β+2-t, (β+1-t)-i) = C(β+1-t, β+1-t) = 1`.
    have hv := vandermonde_range (-m - 1) (m + (β : ℤ) + 2 - (t : ℤ)) ((β : ℤ) + 1 - (t : ℤ))
      (N := β + 2) (by push_cast; omega)
    rw [show ((-m - 1) + (m + (β : ℤ) + 2 - (t : ℤ))) = (β : ℤ) + 1 - (t : ℤ) from by ring] at hv
    rw [hv, show (β : ℤ) + 1 - (t : ℤ) = (((β + 1 - t : ℕ)) : ℤ) from by
        rw [Nat.cast_sub ht]; push_cast; ring,
      cbz_natCast_eq_choose (le_refl (β + 1 - t)), Nat.choose_self, Nat.cast_one, mul_one]
  · -- the term-wise trinomial rewrite + factoring out the `i`-independent `cbz K (m+β+2-t)`.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hb := trinomB K (m + 1 + (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
    rw [show (K : ℤ) - (m + 1 + (i : ℤ)) = (K : ℤ) - m - 1 - (i : ℤ) from by ring,
      show (m + 1 + (i : ℤ)) + ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ)) = m + (β : ℤ) + 2 - (t : ℤ) from by
        ring] at hb
    rw [show cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
          = cbz (-m - 1) (i : ℤ)
              * (cbz (K : ℤ) (m + 1 + (i : ℤ))
                  * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ)))
          from by ring, hb]
    rw [show ((β : ℤ) + 1 - (t : ℤ)) - (i : ℤ) = (β : ℤ) + 1 - (i : ℤ) - (t : ℤ) from by ring]
    ring

/-! ## The main identity. -/

theorem u_core (K L β : ℕ) (m : ℤ) :
    (∑ i ∈ Finset.range (β + 2),
        ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i)
          * cbz (K:ℤ) (m + 1 + (i:ℤ))
          * cbz ((K:ℤ) + (L:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ)))
      = ∑ j ∈ Finset.range (β + 2),
          cbz (K:ℤ) (m + 1 + (j:ℤ)) * cbz (L:ℤ) ((β:ℤ) + 1 - (j:ℤ)) := by
  -- Step 1+2: upper negation, then Vandermonde-split the third factor over a fresh index `t`.
  rw [show (∑ i ∈ Finset.range (β + 2),
            ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i)
              * cbz (K:ℤ) (m + 1 + (i:ℤ))
              * cbz ((K:ℤ) + (L:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ)))
        = ∑ i ∈ Finset.range (β + 2), ∑ t ∈ Finset.range (β + 2),
            cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
              * (cbz (L:ℤ) (t:ℤ)
                  * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ))) from
      Finset.sum_congr rfl (fun i _ => ?_)]
  · -- swap to `t` outer, factor `cbz L t`, collapse the inner `i`-sum via `inner_collapse`.
    rw [Finset.sum_comm]
    rw [show ∑ t ∈ Finset.range (β + 2), ∑ i ∈ Finset.range (β + 2),
              cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                * (cbz (L:ℤ) (t:ℤ)
                    * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)))
          = ∑ t ∈ Finset.range (β + 2),
              cbz (L:ℤ) (t:ℤ) * cbz (K:ℤ) (m + (β:ℤ) + 2 - (t:ℤ)) from
        Finset.sum_congr rfl (fun t ht => ?_)]
    · -- RHS reindex `j = β+1-t` (reflect `range (β+2)`).
      rw [← Finset.sum_range_reflect
            (fun j => cbz (K:ℤ) (m + 1 + (j:ℤ)) * cbz (L:ℤ) ((β:ℤ) + 1 - (j:ℤ))) (β + 2)]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have htβ : t < β + 2 := Finset.mem_range.mp ht
      rw [show ((β + 2 - 1 - t : ℕ) : ℤ) = (β : ℤ) + 1 - (t : ℤ) from by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
      rw [show m + 1 + ((β : ℤ) + 1 - (t : ℤ)) = m + (β : ℤ) + 2 - (t : ℤ) from by ring,
        show (β : ℤ) + 1 - ((β : ℤ) + 1 - (t : ℤ)) = (t : ℤ) from by ring]
      ring
    · -- inner `i`-sum collapse (need `t ≤ β+1`).
      have htβ : t ≤ β + 1 := by have := Finset.mem_range.mp ht; omega
      rw [show ∑ i ∈ Finset.range (β + 2),
                cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                  * (cbz (L:ℤ) (t:ℤ)
                      * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)))
            = cbz (L:ℤ) (t:ℤ)
                * ∑ i ∈ Finset.range (β + 2),
                    cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                      * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)) from by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)]
      rw [inner_collapse K β m t htβ]
  · -- term-wise rewrite for a fixed `i`: upper negation + Vandermonde split.
    rw [show ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i) = cbz (-m - 1) (i:ℤ) from
        (cbz_upper_neg m i).symm]
    have hv := vandermonde_range (L : ℤ) ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ))
      (N := β + 2) (by push_cast; omega)
    rw [show ((L : ℤ) + ((K : ℤ) - m - 1 - (i : ℤ))) = (K : ℤ) + (L : ℤ) - m - 1 - (i : ℤ) from by
        ring] at hv
    rw [← hv, Finset.mul_sum]

end ZhuUCore
