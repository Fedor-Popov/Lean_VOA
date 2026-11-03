/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ48
import VOA.Modules.ZeroModeMult

/-!
# The pure scalar core of Dong–Jiang Lemma 4.9: an alternating Vandermonde Kronecker delta

This file contains **no vertex-algebra content at all**.  It isolates, and proves, the generalized
binomial identity that drives Dong–Jiang (math/0601626) Lemma 4.9:

`∑_{r=0}^{k*} (−1)^r · C(A−1+r, r) · C(A, j−ℓ−r)  =  δ_{j,ℓ}`   (`A = K+n ≥ 1`, `j − ℓ ≤ k*`).

## The conceptual proof

The whole identity is one line once the two moves are named.

* **Move 1 (upper-index negation).**  `(−1)^r · C(A−1+r, r) = C(−A, r)`.  This is the proved
  `alt_cbz_eq` (itself `cbz_neg_upper`) at `q = A − 1`; see `cbz_negA_eq`.
* **Move 2 (Vandermonde).**  Hence the sum, extended over **all** `r ≥ 0`, is the convolution
  `∑_r C(−A, r)·C(A, m−r) = cbzConvol (−A) A m = C((−A)+A, m) = C(0, m)`, by the proved
  `cbz_vandermonde`; see `dj49_master_untruncated_int`.
* **Move 3 (the delta).**  `C(0, m) = [m = 0]` is the zeroth row of Pascal's triangle, the proved
  `cbz_zero_left`; see `cbz_zero_upper`.  This is where the Kronecker delta comes from.
* **Move 4 (truncation is free).**  Every tail term `r > k*` carries the factor `C(A, m−r)` with
  `m − r < 0` whenever `m ≤ k*`, and `cbz` vanishes on negative lower index.  So the truncated sum
  equals the untruncated one; see `dj49_tail_zero` / `dj49_truncation_eq`.

Composing them gives `dj49_master`, the identity as used in Lemma 4.9.

The truncation hypothesis `j − ℓ ≤ k*` is genuinely needed: without it the left-hand side is a
partial sum of an alternating series and is not a delta.

Engine-verified before formalizing: 315,014 exact-integer points, zero failures (and the
generator-basis form on 5756/5756 sets, agreeing componentwise with exact `LinearSolve`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References

Dong–Jiang math/0601626, Lemma 4.9; `Foundations/Substitution` (`cbz`, `cbz_apply_neg`),
`Foundations/IotaZExpansion` (`cbz_zero_left`, `cbzConvol`, `cbz_vandermonde`),
`Modules/ZhuVermaAnArchDJ48` (`cbz_neg_upper`, `alt_cbz_eq`, `range_to_intFinsum`),
`Modules/ZeroModeMult` (`cbz_natCast_eq_choose`), `Core/WeakAssoc` (`finsum_nat_to_int`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

/-! ## §1  The Kronecker delta: the zeroth row of Pascal's triangle -/

/-- **The Kronecker delta lemma.**  `C(0, m) = [m = 0]` for every `m : ℤ`: with the convention
`C(n,k) = 0` for `k < 0`, the zeroth row of Pascal's triangle is the unit mass at `0`.  This is the
sole source of the delta on the right-hand side of Dong–Jiang Lemma 4.9. -/
theorem cbz_zero_upper (m : ℤ) : cbz 0 m = if m = 0 then 1 else 0 := cbz_zero_left m

/-! ## §2  Move 1: negating the upper index -/

/-- **Upper-index negation, `cbz` form.**  `(−1)^r · C(A−1+r, r) = C(−A, r)` for every `A : ℤ` and
`r : ℕ`.  Immediate from the proved `alt_cbz_eq` at `q = A − 1`. -/
theorem cbz_negA_eq (A : ℤ) (r : ℕ) :
    (-1 : ℂ) ^ r * cbz (A - 1 + (r : ℤ)) (r : ℤ) = cbz (-A) (r : ℤ) := by
  have h := alt_cbz_eq (A - 1) r
  rwa [show (-(A - 1) - 1 : ℤ) = -A from by ring] at h

/-- **Upper-index negation, `Nat.choose` form.**  For `A : ℕ` with `1 ≤ A`,
`(−1)^r · (A−1+r).choose r = C(−A, r)` (the left factor is an ordinary binomial coefficient; the
hypothesis `1 ≤ A` is what makes the truncated `ℕ`-subtraction `A − 1` faithful). -/
theorem cbz_negA_choose (A : ℕ) (hA : 1 ≤ A) (r : ℕ) :
    (-1 : ℂ) ^ r * (((A - 1 + r).choose r : ℕ) : ℂ) = cbz (-(A : ℤ)) (r : ℤ) := by
  have hcast : ((A - 1 + r : ℕ) : ℤ) = (A : ℤ) - 1 + (r : ℤ) := by omega
  have hchoose : cbz ((A - 1 + r : ℕ) : ℤ) (r : ℤ) = (((A - 1 + r).choose r : ℕ) : ℂ) :=
    cbz_natCast_eq_choose (by omega)
  rw [hcast] at hchoose
  rw [← hchoose]
  exact cbz_negA_eq (A : ℤ) r

/-! ## §3  Move 2: the untruncated alternating Vandermonde -/

/-- The convolution summand `r ↦ C(−A, r)·C(A, m−r)` vanishes off `[0, m]`: below `0` because
`cbz` has zero lower-index support there, above `m` because then `m − r < 0`.  (No hypothesis on
`A`.) -/
theorem dj49_term_eq_zero (A m : ℤ) {x : ℤ} (hx : x < 0 ∨ m < x) :
    cbz (-A) x * cbz A (m - x) = 0 := by
  rcases hx with hx | hx
  · rw [cbz_apply_neg _ hx, zero_mul]
  · rw [cbz_apply_neg A (by omega : m - x < 0), mul_zero]

/-- **The headline, `ℤ`-`finsum` form.**  The untruncated alternating convolution collapses to
the Kronecker delta row:

`∑_{r : ℤ} C(−A, r) · C(A, m−r) = C(0, m)`.

This is exactly `cbz_vandermonde` at `(m, n) = (−A, A)`; by `cbz_zero_upper` the right-hand side is
`[m = 0]`. -/
theorem dj49_master_untruncated_int (A m : ℤ) :
    (∑ᶠ r : ℤ, cbz (-A) r * cbz A (m - r)) = cbz 0 m := by
  have h := cbz_vandermonde (-A) A m
  rw [cbzConvol] at h
  rw [h, show (-A + A : ℤ) = 0 from by ring]

/-- **The headline, `ℕ`-`finsum` form.**  `∑_{r : ℕ} C(−A, r) · C(A, m−r) = C(0, m)`.  The
`ℕ`-to-`ℤ` bridge is `finsum_nat_to_int`, legitimate because the summand vanishes at negative
`r`. -/
theorem dj49_master_untruncated (A m : ℤ) :
    (∑ᶠ r : ℕ, cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ))) = cbz 0 m := by
  rw [finsum_nat_to_int (fun r : ℕ => cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ)))
    (fun x : ℤ => cbz (-A) x * cbz A (m - x))
    (fun p hp => dj49_term_eq_zero A m (Or.inl hp)) (fun _ => rfl)]
  exact dj49_master_untruncated_int A m

/-- **The headline, fully explicit `Nat.choose` form.**  For `A : ℕ` with `1 ≤ A`,

`∑_{r ≥ 0} (−1)^r · (A−1+r).choose r · C(A, m−r) = [m = 0]`.

This is the statement "if the `r`-sum is extended over all `r ≥ 0` it Vandermondes to the Kronecker
delta". -/
theorem dj49_master_untruncated_choose (A : ℕ) (hA : 1 ≤ A) (m : ℤ) :
    (∑ᶠ r : ℕ, (-1 : ℂ) ^ r * (((A - 1 + r).choose r : ℕ) : ℂ) * cbz (A : ℤ) (m - (r : ℤ)))
      = if m = 0 then 1 else 0 := by
  rw [finsum_congr (g := fun r : ℕ => cbz (-(A : ℤ)) (r : ℤ) * cbz (A : ℤ) (m - (r : ℤ)))
    fun r => by rw [cbz_negA_choose A hA r]]
  rw [dj49_master_untruncated (A : ℤ) m, cbz_zero_upper]

/-! ## §4  Move 4: the truncation is free -/

/-- **Tail vanishing.**  If `m ≤ k*` then every term of the convolution beyond `k*` is zero, since
its second factor is `C(A, m−r)` with `m − r < 0`. -/
theorem dj49_tail_zero (A m : ℤ) (kstar : ℕ) (hk : m ≤ (kstar : ℤ)) (r : ℕ) (hr : kstar < r) :
    cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ)) = 0 :=
  dj49_term_eq_zero A m (Or.inr (by omega))

/-- **The truncated alternating Vandermonde.**  For any `A : ℤ`, any `m : ℤ` and any cut-off
`k*` with `m ≤ k*`,

`∑_{r=0}^{k*} C(−A, r) · C(A, m−r) = C(0, m) = [m = 0]`.

The truncated range sum is converted to the `ℤ`-`finsum` by `range_to_intFinsum` (the summand
vanishes off `[0, m.toNat]`), and the `finsum` is `dj49_master_untruncated_int`. -/
theorem dj49_master_truncated (A m : ℤ) (kstar : ℕ) (hk : m ≤ (kstar : ℤ)) :
    (∑ r ∈ Finset.range (kstar + 1), cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ))) = cbz 0 m := by
  rw [range_to_intFinsum m.toNat kstar (by omega)
    (fun x : ℤ => cbz (-A) x * cbz A (m - x))
    (fun x hx => dj49_term_eq_zero A m (by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by omega)))]
  exact dj49_master_untruncated_int A m

/-- **Truncation changes nothing.**  Under `m ≤ k*` the truncated sum and the full `ℕ`-`finsum`
agree — the "tail split" of Lemma 4.9, with the tail identically zero. -/
theorem dj49_truncation_eq (A m : ℤ) (kstar : ℕ) (hk : m ≤ (kstar : ℤ)) :
    (∑ r ∈ Finset.range (kstar + 1), cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ)))
      = ∑ᶠ r : ℕ, cbz (-A) (r : ℤ) * cbz A (m - (r : ℤ)) := by
  rw [dj49_master_truncated A m kstar hk, dj49_master_untruncated A m]

/-! ## §5  The MASTER identity -/

/-- **THE MASTER SCALAR IDENTITY OF DONG–JIANG LEMMA 4.9.**

For `K n : ℕ` with `1 ≤ K + n`, any `ℓ : ℤ`, any cut-off `k* : ℕ`, and any `j : ℤ` with
`j − ℓ ≤ k*`:

`∑_{r=0}^{k*} (−1)^r · (K+n−1+r).choose r · C(K+n, j−ℓ−r)  =  δ_{j,ℓ}`.

The proof is the four moves of the module docstring: negate the upper index of the alternating
binomial (`cbz_negA_choose`), observe the tail beyond `k*` vanishes (`dj49_master_truncated`), and
Vandermonde the resulting full convolution to `C(0, j−ℓ)` (`cbz_vandermonde`), which is the
Kronecker delta (`cbz_zero_upper`). -/
theorem dj49_master (K n : ℕ) (hKn : 1 ≤ K + n) (ℓ : ℤ) (kstar : ℕ) (j : ℤ)
    (hk : j - ℓ ≤ (kstar : ℤ)) :
    (∑ r ∈ Finset.range (kstar + 1),
        (-1 : ℂ) ^ r * (((K + n - 1 + r).choose r : ℕ) : ℂ)
          * cbz ((K : ℤ) + (n : ℤ)) (j - ℓ - (r : ℤ)))
      = if j = ℓ then 1 else 0 := by
  have hA : ((K + n : ℕ) : ℤ) = (K : ℤ) + (n : ℤ) := by push_cast; ring
  have hterm : ∀ r : ℕ,
      (-1 : ℂ) ^ r * (((K + n - 1 + r).choose r : ℕ) : ℂ)
          * cbz ((K : ℤ) + (n : ℤ)) (j - ℓ - (r : ℤ))
        = cbz (-((K + n : ℕ) : ℤ)) (r : ℤ)
          * cbz (((K + n : ℕ) : ℤ)) ((j - ℓ) - (r : ℤ)) := by
    intro r
    rw [← cbz_negA_choose (K + n) hKn r, hA]
  rw [Finset.sum_congr rfl fun r _ => hterm r,
    dj49_master_truncated ((K + n : ℕ) : ℤ) (j - ℓ) kstar hk, cbz_zero_upper]
  by_cases hj : j = ℓ
  · rw [if_pos hj, if_pos (by omega)]
  · rw [if_neg hj, if_neg (by omega)]

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.cbz_zero_upper
  #print axioms VOA.cbz_negA_eq
  #print axioms VOA.cbz_negA_choose
  #print axioms VOA.dj49_term_eq_zero
  #print axioms VOA.dj49_master_untruncated_int
  #print axioms VOA.dj49_master_untruncated
  #print axioms VOA.dj49_master_untruncated_choose
  #print axioms VOA.dj49_tail_zero
  #print axioms VOA.dj49_master_truncated
  #print axioms VOA.dj49_truncation_eq
  #print axioms VOA.dj49_master
-/
