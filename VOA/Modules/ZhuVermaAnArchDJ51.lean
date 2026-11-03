/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuMuIdentity

/-!
# Dong–Jiang Appendix Proposition 5.1, in Laurent coefficients

Dong–Jiang (math/0601626, Appendix Prop. 5.1) set, for `m, n ∈ ℤ₊`,

`A_{m,n}(z) = ∑_{i=0}^{m} (−1)^i C(n+i,i) (1+z)^{n+1}/z^{n+i+1}`
`           − ∑_{i=0}^{n} (−1)^m C(m+i,i) (1+z)^i /z^{m+i+1}`

and prove `A_{m,n}(z) = 1`.  Since the coefficient of `z^r` in `(1+z)^a/z^b` is `C(a, r+b)`,
this is exactly the statement `dj51_coeff` below: for all `p₁ p₂ : ℕ` and `r : ℤ`,

`∑_{i=0}^{p₁} (−1)^i C(p₂+i,i) C(p₂+1, r+p₂+i+1) − ∑_{i=0}^{p₂} (−1)^{p₁} C(p₁+i,i) C(i, r+p₁+i+1)`
`  = δ_{r,0}`.

The file is pure `cbz` combinatorics: no vertex-algebra content whatsoever.

## Proof outline

Dong–Jiang argue by `A_{m,n} = A_{m,n+1}` plus a geometric sum.  The route taken here is a
*single* induction on `p₁`, which is cleaner at the level of coefficients.  Applying binomial
symmetry (`ZhuMu.cbz_symm`) to the three `cbz` factors with a natural-number top index turns the
statement into `dj51_symm`, in which the second binomial of each summand no longer depends on the
summation index in its top slot:

`∑_{i=0}^{m} (−1)^i C(n+i,i) C(n+1, −r−i) − (−1)^m ∑_{i=0}^{n} C(m+i,m) C(i, −r−m−1) = δ_{r,0}`.

* the `m = 0` case is the **hockey-stick identity with a defect**, `cbz_range_hockey`:
  `∑_{i=0}^{n} C(i,k) = C(n+1,k+1) − [k = −1]` (the defect at `k = −1` *is* the `δ_{r,0}`);
* the `m ↦ m+1` step is the **Pascal convolution** `cbz_pascalConvol`:
  `∑_{i=0}^{n} C(m+1+i,m+1) C(i,M−1) + ∑_{i=0}^{n} C(m+i,m) C(i,M) = C(n+m+1,m+1) C(n+1,M)`.

Both auxiliary identities are proved by induction on `n` using only `cbz_pascal_up`.

Engine-verified before formalizing: zero failures over `0 ≤ p₁, p₂ ≤ 7`, `−14 ≤ r ≤ 14`
(and likewise for the two auxiliary identities).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References

Dong–Jiang math/0601626, Appendix Prop. 5.1; `Foundations/Substitution` (`cbz`, `cbz_pascal`),
`Foundations/IotaZExpansion` (`cbz_pascal_up`, `cbz_zero_left`),
`Modules/ZhuMuIdentity` (`ZhuMu.cbz_symm`), `Modules/ZeroModeMult` (`cbz_natCast_eq_choose`).
-/

namespace VOA

open scoped BigOperators

/-! ## §1  Two `cbz` micro-lemmas -/

/-- The diagonal binomial is `1`: `C(N,N) = 1` for `N : ℕ`. -/
theorem cbz_self (N : ℕ) : cbz (N : ℤ) (N : ℤ) = 1 := by
  rw [cbz_natCast_eq_choose (le_refl N), Nat.choose_self, Nat.cast_one]

/-- `C(1,k) = C(0,k) + C(0,k−1)`, i.e. the first row of Pascal's triangle written through
`cbz_pascal_up` at top index `0`. -/
theorem cbz_one_row (k : ℤ) : cbz (1 : ℤ) k = cbz (0 : ℤ) k + cbz (0 : ℤ) (k - 1) := by
  have h := cbz_pascal_up (0 : ℤ) k
  rwa [zero_add] at h

/-! ## §2  The hockey-stick identity with a defect

`∑_{i=0}^{n} C(i,k) = C(n+1,k+1) − [k = −1]`.  For `k ≥ 0` this is the usual hockey stick; the
correction term appears at `k = −1`, where the left side is `0` while `C(n+1,0) = 1`.  This single
defect is the source of the Kronecker delta in `dj51_coeff`. -/

/-- **Hockey stick with a defect.**  `∑_{i=0}^{n} C(i,k) = C(n+1,k+1) − [k = −1]`, for all
`n : ℕ` and `k : ℤ` (with the convention `C(·,k) = 0` for `k < 0`). -/
theorem cbz_range_hockey (n : ℕ) (k : ℤ) :
    (∑ i ∈ Finset.range (n + 1), cbz (i : ℤ) k)
      = cbz ((n : ℤ) + 1) (k + 1) - (if k = -1 then 1 else 0) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, Nat.cast_zero, zero_add, cbz_one_row, cbz_zero_left (k + 1)]
    have hk : (if k + 1 = 0 then (1 : ℂ) else 0) = if k = -1 then (1 : ℂ) else 0 := by
      by_cases h : k = -1
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [hk, show k + 1 - 1 = k from by ring]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hp := cbz_pascal_up ((n : ℤ) + 1) (k + 1)
    rw [show k + 1 - 1 = k from by ring] at hp
    rw [show (((n + 1 : ℕ) : ℤ) + 1) = ((n : ℤ) + 1) + 1 from by push_cast; ring, hp,
      show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 from by push_cast; ring]
    ring

/-! ## §3  The Pascal convolution driving the `p₁`-induction -/

/-- **The Pascal convolution.**  For all `m n : ℕ` and `M : ℤ`,

`∑_{i=0}^{n} C(m+1+i, m+1) C(i, M−1) + ∑_{i=0}^{n} C(m+i, m) C(i, M) = C(n+m+1, m+1) C(n+1, M)`.

Proved by induction on `n`: the base case is `C(1,M) = C(0,M) + C(0,M−1)`, and the step is
Pascal in both slots, `C(n+m+2,m+1) = C(n+m+1,m+1) + C(n+m+1,m)` and
`C(n+2,M) = C(n+1,M) + C(n+1,M−1)`. -/
theorem cbz_pascalConvol (m n : ℕ) (M : ℤ) :
    (∑ i ∈ Finset.range (n + 1), cbz ((m : ℤ) + 1 + (i : ℤ)) ((m : ℤ) + 1) * cbz (i : ℤ) (M - 1))
      + (∑ i ∈ Finset.range (n + 1), cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) M)
      = cbz ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) * cbz ((n : ℤ) + 1) M := by
  induction n with
  | zero =>
    have hm1 : cbz ((m : ℤ) + 1) ((m : ℤ) + 1) = 1 := by
      have h := cbz_self (m + 1)
      rwa [show (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 from by push_cast; ring] at h
    have hm0 : cbz (m : ℤ) (m : ℤ) = 1 := cbz_self m
    simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, zero_add]
    rw [hm0, hm1, cbz_one_row M]
    ring
  | succ n ih =>
    have hcast : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
    -- Peel the top term off the first sum, with the index in normal form.
    have e1 : (∑ i ∈ Finset.range (n + 1 + 1),
          cbz ((m : ℤ) + 1 + (i : ℤ)) ((m : ℤ) + 1) * cbz (i : ℤ) (M - 1))
        = (∑ i ∈ Finset.range (n + 1),
            cbz ((m : ℤ) + 1 + (i : ℤ)) ((m : ℤ) + 1) * cbz (i : ℤ) (M - 1))
          + cbz ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) * cbz ((n : ℤ) + 1) (M - 1) := by
      rw [Finset.sum_range_succ, hcast,
        show ((m : ℤ) + 1 + ((n : ℤ) + 1)) = (n : ℤ) + (m : ℤ) + 1 + 1 from by ring]
    -- Peel the top term off the second sum.
    have e2 : (∑ i ∈ Finset.range (n + 1 + 1),
          cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) M)
        = (∑ i ∈ Finset.range (n + 1),
            cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) M)
          + cbz ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) * cbz ((n : ℤ) + 1) M := by
      rw [Finset.sum_range_succ, hcast,
        show ((m : ℤ) + ((n : ℤ) + 1)) = (n : ℤ) + (m : ℤ) + 1 from by ring]
    -- Pascal in the top slot.
    have htop := cbz_pascal_up ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1)
    rw [show ((m : ℤ) + 1 - 1) = (m : ℤ) from by ring] at htop
    -- Pascal in the bottom slot.
    have hbot := cbz_pascal_up ((n : ℤ) + 1) M
    rw [e1, e2, hcast,
      show (((n : ℤ) + 1) + (m : ℤ) + 1) = (n : ℤ) + (m : ℤ) + 1 + 1 from by ring]
    linear_combination ih - cbz ((n : ℤ) + 1) M * htop
      - cbz ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) * hbot

/-! ## §4  The symmetrised form of Prop. 5.1 -/

/-- **Prop. 5.1, symmetrised.**  For all `m n : ℕ` and `r : ℤ`,

`∑_{i=0}^{m} (−1)^i C(n+i,i) C(n+1, −r−i) − (−1)^m ∑_{i=0}^{n} C(m+i,m) C(i, −r−m−1) = δ_{r,0}`.

Induction on `m`.  The base `m = 0` is `cbz_range_hockey` at `k = −r−1`; the step is
`cbz_pascalConvol` at `M = −r−m−1`. -/
theorem dj51_symm (m n : ℕ) (r : ℤ) :
    (∑ i ∈ Finset.range (m + 1),
        (-1 : ℂ) ^ i * cbz ((n : ℤ) + (i : ℤ)) (i : ℤ) * cbz ((n : ℤ) + 1) (-r - (i : ℤ)))
      - (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ m * cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) (-r - (m : ℤ) - 1))
    = if r = 0 then 1 else 0 := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one]
    have hleft : (-1 : ℂ) ^ (0 : ℕ) * cbz ((n : ℤ) + ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)
        * cbz ((n : ℤ) + 1) (-r - ((0 : ℕ) : ℤ)) = cbz ((n : ℤ) + 1) (-r) := by
      rw [Nat.cast_zero, add_zero, cbz_zero, sub_zero]
      ring
    have hright : ∀ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (0 : ℕ) * cbz (((0 : ℕ) : ℤ) + (i : ℤ)) ((0 : ℕ) : ℤ)
            * cbz (i : ℤ) (-r - ((0 : ℕ) : ℤ) - 1) = cbz (i : ℤ) (-r - 1) := by
      intro i _
      rw [Nat.cast_zero, cbz_zero, sub_zero]
      ring
    rw [hleft, Finset.sum_congr rfl hright, cbz_range_hockey n (-r - 1),
      show (-r - 1 + 1) = -r from by ring]
    have hd : (if (-r - 1 : ℤ) = -1 then (1 : ℂ) else 0) = if r = 0 then (1 : ℂ) else 0 := by
      by_cases h : r = 0
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [hd]
    ring
  | succ m ih =>
    -- Peel the new top term off the first sum.
    rw [Finset.sum_range_succ]
    have hcast : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
    -- The new top term of the first sum.
    have hnew : (-1 : ℂ) ^ (m + 1) * cbz ((n : ℤ) + (((m + 1 : ℕ)) : ℤ)) (((m + 1 : ℕ)) : ℤ)
        * cbz ((n : ℤ) + 1) (-r - (((m + 1 : ℕ)) : ℤ))
        = (-1 : ℂ) ^ (m + 1) * (cbz ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1)
            * cbz ((n : ℤ) + 1) (-r - (m : ℤ) - 1)) := by
      rw [hcast, show ((n : ℤ) + ((m : ℤ) + 1)) = (n : ℤ) + (m : ℤ) + 1 from by ring,
        show (-r - ((m : ℤ) + 1)) = -r - (m : ℤ) - 1 from by ring]
      ring
    rw [hnew]
    -- The second sum at `m+1`, rewritten to match `cbz_pascalConvol`.
    have hsnd : (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ (m + 1)
          * cbz ((((m + 1 : ℕ)) : ℤ) + (i : ℤ)) ((((m + 1 : ℕ))) : ℤ)
          * cbz (i : ℤ) (-r - ((((m + 1 : ℕ))) : ℤ) - 1))
        = (-1 : ℂ) ^ (m + 1) * (∑ i ∈ Finset.range (n + 1),
            cbz ((m : ℤ) + 1 + (i : ℤ)) ((m : ℤ) + 1)
              * cbz (i : ℤ) ((-r - (m : ℤ) - 1) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcast, show (-r - ((m : ℤ) + 1) - 1) = (-r - (m : ℤ) - 1) - 1 from by ring]
      ring
    rw [hsnd]
    -- The second sum at `m`, pulled out of the alternating sign.
    have hsnd' : (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ m
          * cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) (-r - (m : ℤ) - 1))
        = (-1 : ℂ) ^ m * (∑ i ∈ Finset.range (n + 1),
            cbz ((m : ℤ) + (i : ℤ)) (m : ℤ) * cbz (i : ℤ) (-r - (m : ℤ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsnd'] at ih
    -- The convolution identity at `M = −r−m−1`.
    have hconv := cbz_pascalConvol m n (-r - (m : ℤ) - 1)
    -- Assemble.
    rw [← ih]
    have hexp : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ m) := by rw [pow_succ]; ring
    rw [hexp]
    linear_combination ((-1 : ℂ) ^ m) * hconv

/-! ## §5  The target: Dong–Jiang Prop. 5.1 in Laurent coefficients -/

/-- **Dong–Jiang, Appendix Prop. 5.1 (coefficient form).**  For all `p₁ p₂ : ℕ` and `r : ℤ`,

`∑_{i=0}^{p₁} (−1)^i C(p₂+i,i) C(p₂+1, r+p₂+i+1) − ∑_{i=0}^{p₂} (−1)^{p₁} C(p₁+i,i) C(i,r+p₁+i+1)`
`  = δ_{r,0}`,

i.e. the coefficient of `z^r` in `A_{p₁,p₂}(z)` is `δ_{r,0}`, which is Dong–Jiang's
`A_{m,n}(z) = 1`.

Obtained from `dj51_symm` by three applications of binomial symmetry `ZhuMu.cbz_symm`:
`C(p₂+1, r+p₂+i+1) = C(p₂+1, −r−i)`, `C(p₁+i,i) = C(p₁+i,p₁)` and
`C(i, r+p₁+i+1) = C(i, −r−p₁−1)`. -/
theorem dj51_coeff (p₁ p₂ : ℕ) (r : ℤ) :
    (∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + i) (i : ℤ) * cbz ((p₂ : ℤ) + 1) (r + p₂ + i + 1))
      - (∑ i ∈ Finset.range (p₂ + 1),
        (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + i) (i : ℤ) * cbz (i : ℤ) (r + p₁ + i + 1))
    = if r = 0 then 1 else 0 := by
  have hfst : ∀ i ∈ Finset.range (p₁ + 1),
      (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ) * cbz ((p₂ : ℤ) + 1) (r + p₂ + i + 1)
        = (-1 : ℂ) ^ i * cbz ((p₂ : ℤ) + (i : ℤ)) (i : ℤ) * cbz ((p₂ : ℤ) + 1) (-r - (i : ℤ)) := by
    intro i _
    have hs := ZhuMu.cbz_symm (p₂ + 1) (r + (p₂ : ℤ) + (i : ℤ) + 1)
    rw [show (((p₂ + 1 : ℕ) : ℤ)) = (p₂ : ℤ) + 1 from by push_cast; ring,
      show ((p₂ : ℤ) + 1 - (r + (p₂ : ℤ) + (i : ℤ) + 1)) = -r - (i : ℤ) from by ring] at hs
    rw [hs]
  have hsnd : ∀ i ∈ Finset.range (p₂ + 1),
      (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (i : ℤ) * cbz (i : ℤ) (r + p₁ + i + 1)
        = (-1 : ℂ) ^ p₁ * cbz ((p₁ : ℤ) + (i : ℤ)) (p₁ : ℤ)
            * cbz (i : ℤ) (-r - (p₁ : ℤ) - 1) := by
    intro i _
    have hs₁ := ZhuMu.cbz_symm (p₁ + i) (i : ℤ)
    rw [show (((p₁ + i : ℕ) : ℤ)) = (p₁ : ℤ) + (i : ℤ) from by push_cast; ring,
      show ((p₁ : ℤ) + (i : ℤ) - (i : ℤ)) = (p₁ : ℤ) from by ring] at hs₁
    have hs₂ := ZhuMu.cbz_symm i (r + (p₁ : ℤ) + (i : ℤ) + 1)
    rw [show ((i : ℤ) - (r + (p₁ : ℤ) + (i : ℤ) + 1)) = -r - (p₁ : ℤ) - 1 from by ring] at hs₂
    rw [hs₁, hs₂]
  rw [Finset.sum_congr rfl hfst, Finset.sum_congr rfl hsnd]
  exact dj51_symm p₁ p₂ r

end VOA
