/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.IotaZExpansion
import VOA.Core.Skew

/-!
# The alternating Vandermonde convolution `∑ₛ (−1)ˢ C(A,s) C(B−s, L−s) = C(B−A, L)`

This is the scalar engine behind the residue form of skew symmetry modulo the Dong–Jiang ideal:
when `Y(v,z)u` is rewritten through `Y(u,z)v` by skew symmetry, the two generalized binomials
`C(wt v + m, s)` (from the residue) and `C(E − t, ℓ − t)` (from the `L₋₁`-tower collapse) convolve
with an alternating sign, and collapse to the single binomial `C(wt u + P − N − 2, ℓ + P)`.

Generating-function proof (for orientation only; the Lean proof is the Pascal induction below):
`∑_L (∑ₛ (−1)ˢ C(A,s) C(B−s,L−s)) x^L = (1+x)^B ∑ₛ C(A,s)(−x/(1+x))^s = (1+x)^{B−A}`.

The sum is written as a `finsum` over `ℤ`; it is always finite because `C(A,s) = 0` for `s < 0` and
`C(B−s, L−s) = 0` for `s > L`, so the support sits inside `Set.Icc 0 L`.  The alternating sign is
the repo's `sgn : ℤ → ℂ` (`sgn n = if Even n then 1 else −1`).

Engine-verified before formalizing: `0` failures over `0 ≤ A ≤ 7`, `−8 ≤ B ≤ 10`, `−4 ≤ L ≤ 10`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (the skew step of Lemma 2.3); `Foundations/IotaZExpansion`
(`cbz_pascal_up`, `cbz_vandermonde`), `Foundations/Substitution` (`cbz`, `cbz_pascal`),
`Core/Skew` (`sgn`, `sgn_succ`).
-/

namespace VOA

open scoped BigOperators

/-! ## Finiteness of the alternating convolution family. -/

/-- The alternating convolution family `s ↦ sgn s · C(A,s) · C(B−s, L−s)` is supported in
`Set.Icc 0 L`, hence has finite support. -/
theorem cbzAltVan_support_finite (A B L : ℤ) :
    (Function.support fun s : ℤ => sgn s * cbz A s * cbz (B - s) (L - s)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc 0 L) ?_
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact hs (by rw [cbz_apply_neg A hlt, mul_zero, zero_mul])
  · by_contra hgt
    push_neg at hgt
    exact hs (by rw [cbz_apply_neg (B - s) (by omega), mul_zero])

/-! ## The identity. -/

/-- **The alternating Vandermonde convolution**:
`∑ₛ (−1)ˢ · C(A,s) · C(B−s, L−s) = C(B−A, L)` for `A : ℕ` and all integers `B, L`.

Proved by induction on `A` with Pascal's rule: the `A+1` step splits `C(A+1,s)` into
`C(A,s) + C(A,s−1)`, the second piece reindexes (`s ↦ s+1`, flipping the sign) to the inductive
hypothesis at `(B−1, L−1)`, and `C(B−A,L) − C(B−A−1,L−1) = C(B−A−1,L)` is Pascal again. -/
theorem cbz_alt_vandermonde (A : ℕ) (B L : ℤ) :
    (∑ᶠ s : ℤ, sgn s * cbz (A : ℤ) s * cbz (B - s) (L - s)) = cbz (B - (A : ℤ)) L := by
  induction A generalizing B L with
  | zero =>
    have hterm : ∀ s : ℤ, sgn s * cbz ((0 : ℕ) : ℤ) s * cbz (B - s) (L - s)
        = if s = 0 then cbz B L else 0 := by
      intro s
      rw [Nat.cast_zero, cbz_zero_left]
      split_ifs with h
      · subst h
        simp [sgn]
      · rw [mul_zero, zero_mul]
    rw [finsum_congr hterm, finsum_eq_single _ 0 (fun s hs => if_neg hs), if_pos rfl]
    simp
  | succ A ih =>
    -- split by Pascal
    have hsplit : ∀ s : ℤ, sgn s * cbz ((A + 1 : ℕ) : ℤ) s * cbz (B - s) (L - s)
        = sgn s * cbz (A : ℤ) s * cbz (B - s) (L - s)
          + sgn s * cbz (A : ℤ) (s - 1) * cbz (B - s) (L - s) := by
      intro s
      rw [show ((A + 1 : ℕ) : ℤ) = (A : ℤ) + 1 from by push_cast; ring, cbz_pascal_up]
      ring
    have hfin₁ := cbzAltVan_support_finite (A : ℤ) B L
    have hfin₂ : (Function.support fun s : ℤ =>
        sgn s * cbz (A : ℤ) (s - 1) * cbz (B - s) (L - s)).Finite := by
      refine Set.Finite.subset (Set.finite_Icc 0 (L + 1)) ?_
      intro s hs
      rw [Function.mem_support] at hs
      rw [Set.mem_Icc]
      constructor
      · by_contra hlt
        push_neg at hlt
        exact hs (by rw [cbz_apply_neg (A : ℤ) (by omega), mul_zero, zero_mul])
      · by_contra hgt
        push_neg at hgt
        exact hs (by rw [cbz_apply_neg (B - s) (by omega), mul_zero])
    rw [finsum_congr hsplit, finsum_add_distrib hfin₁ hfin₂, ih B L]
    -- reindex the second sum by `s ↦ s + 1`
    have hreidx : (∑ᶠ s : ℤ, sgn s * cbz (A : ℤ) (s - 1) * cbz (B - s) (L - s))
        = -(∑ᶠ s : ℤ, sgn s * cbz (A : ℤ) s * cbz ((B - 1) - s) ((L - 1) - s)) := by
      rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun s : ℤ => sgn s * cbz (A : ℤ) (s - 1) * cbz (B - s) (L - s))]
      rw [← finsum_neg_distrib]
      refine finsum_congr fun s => ?_
      show sgn (s + 1) * cbz (A : ℤ) ((s + 1) - 1) * cbz (B - (s + 1)) (L - (s + 1)) = _
      rw [sgn_succ, show ((s + 1) - 1 : ℤ) = s from by ring,
        show (B - (s + 1) : ℤ) = (B - 1) - s from by ring,
        show (L - (s + 1) : ℤ) = (L - 1) - s from by ring]
      ring
    rw [hreidx, ih (B - 1) (L - 1)]
    -- Pascal on the target
    rw [show (B - ((A + 1 : ℕ) : ℤ)) = (B - (A : ℤ)) - 1 from by push_cast; ring]
    rw [show (B - 1 - (A : ℤ)) = (B - (A : ℤ)) - 1 from by ring]
    have hp := cbz_pascal (B - (A : ℤ)) L
    linear_combination hp

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.cbz_alt_vandermonde
-/
