/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ23Final
import VOA.Modules.ZhuMuIdentity

/-!
# Dong–Jiang Lemma `la4.8` — the boundary companion of Lemma 2.3

Dong–Jiang's Lemma 2.3 assumes `p₁, p₂ ≥ 0`.  Their Lemma `la4.8` covers the two boundary regimes
that occur in Lemma 4.7 when one of the two mode compositions is identically zero:

* `p₁ ≥ 0 > p₂` : `u ∗^{p₁+p₂−m}_{m,p₁} v ≡ Res_z (1+z)^{wt u−1+m−p₂} Y(u,z)v`;
* `p₁ < 0 ≤ p₂` : `−v ∗^{p₁+p₂−m}_{m,p₂} u ≡ Res_z (1+z)^{wt u−1+m−p₂} Y(u,z)v`,

both `(mod O'_{p₁+p₂−m,m})`.  Only one of `p₁, p₂` is negative, and it never appears as a `∗`-index —
so both statements are phrased here with **`ℕ` indices only**, the negativity being recorded as the
single inequality `N + m < p` (`p = m + N − (the negative index)` forces `p > N + m`).

## Why this is cheap

Dong–Jiang derive `la4.8` from their Lemma 2.4 (high-pole residues lie in `O'`) at **general `m`** —
which the repo has only at `m = 0`.  That detour is unnecessary: after `cbz_neg_upper`
(`C(n,k) = (−1)^k C(k−n−1,k)`) the alternating binomial `(−1)ⁱ C(q+i,i)` becomes the *ordinary*
`C(−q−1, i)`, which vanishes past `i = −q−1`, so the sum is already complete and both regimes
collapse to a Vandermonde:

* case 1 to the plain `cbz_vandermonde` (after the reflection `i ↦ J − i` and `ZhuMu.cbz_symm`);
* case 2 to `cbz_alt_vandermonde`, after `resHom_skew_mod_Onm` has swapped the arguments.

Engine-verified before formalizing: `0` failures for `−8 ≤ D ≤ 8`, `0 ≤ p ≤ 8`, the negative index in
`[−6,−1]`, `0 ≤ m ≤ 4`, `−6 ≤ ℓ ≤ 10`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemma `la4.8`), §2 (Lemmas 2.3, 2.4), Appendix;
`ZhuVermaAnArchResSkew` (`resHom_skew_mod_Onm`, `resFull`, `resHom_eq_resFull`),
`ZhuVermaAnArchAltVandermonde` (`cbz_alt_vandermonde`), `Foundations/IotaZExpansion`
(`cbz_vandermonde`), `ZhuMuIdentity` (`ZhuMu.cbz_symm`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Negating the upper index. -/

/-- **Upper-index negation** `C(n,k) = (−1)ᵏ·C(k−n−1, k)` — the falling factorial at `n` is, up to
sign, the falling factorial at `k−n−1` reindexed by `i ↦ k−1−i`. -/
theorem cbz_neg_upper (n : ℤ) (k : ℕ) :
    cbz n (k : ℤ) = (-1 : ℂ) ^ k * cbz ((k : ℤ) - n - 1) (k : ℤ) := by
  have hstep : ∏ i ∈ Finset.range k, ((((k : ℤ) - n - 1 : ℤ) : ℂ) - (i : ℂ))
      = ∏ i ∈ Finset.range k, ((-1 : ℂ) * ((n : ℂ) - (i : ℂ))) := by
    conv_lhs => rw [← Finset.prod_range_reflect
      (fun i : ℕ => ((((k : ℤ) - n - 1 : ℤ) : ℂ) - (i : ℂ))) k]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have h1 : (1 : ℕ) ≤ k := by omega
    have hik : (i : ℕ) ≤ k - 1 := by omega
    have hcast : ((k - 1 - i : ℕ) : ℂ) = (k : ℂ) - 1 - (i : ℂ) := by
      rw [Nat.cast_sub hik, Nat.cast_sub h1]
      push_cast; ring
    show ((((k : ℤ) - n - 1 : ℤ) : ℂ) - ((k - 1 - i : ℕ) : ℂ)) = _
    rw [hcast]
    push_cast; ring
  have hprod : ∏ i ∈ Finset.range k, ((((k : ℤ) - n - 1 : ℤ) : ℂ) - (i : ℂ))
      = (-1 : ℂ) ^ k * ∏ i ∈ Finset.range k, ((n : ℂ) - (i : ℂ)) := by
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hc1 : cbz n (k : ℤ) = gBinom n k := by
    rw [cbz, if_pos (Int.natCast_nonneg k), Int.toNat_natCast]
  have hc2 : cbz ((k : ℤ) - n - 1) (k : ℤ) = gBinom ((k : ℤ) - n - 1) k := by
    rw [cbz, if_pos (Int.natCast_nonneg k), Int.toNat_natCast]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, show k + k = 2 * k from by ring, pow_mul]; norm_num
  rw [hc1, hc2, gBinom, gBinom, hprod, ← mul_div_assoc, ← mul_assoc, hsq, one_mul]

/-- The alternating binomial `(−1)ⁱ·C(q+i, i)` is the ordinary `C(−q−1, i)`. -/
theorem alt_cbz_eq (q : ℤ) (i : ℕ) :
    (-1 : ℂ) ^ i * cbz (q + (i : ℤ)) (i : ℤ) = cbz (-q - 1) (i : ℤ) := by
  have h := cbz_neg_upper (q + (i : ℤ)) i
  have hsq : ((-1 : ℂ) ^ i) * ((-1 : ℂ) ^ i) = 1 := by
    rw [← pow_add, show i + i = 2 * i from by ring, pow_mul]; norm_num
  rw [h, show ((i : ℤ) - (q + (i : ℤ)) - 1) = -q - 1 from by ring, ← mul_assoc, hsq, one_mul]

/-! ## Converting the truncated sums to `ℤ`-`finsum`s. -/

/-- A `Finset.range` sum whose summand carries a factor `cbz (J:ℤ) i` (with `J ≤ p`) is the
corresponding `ℤ`-`finsum`. -/
theorem range_to_intFinsum (J p : ℕ) (hJp : J ≤ p) (F : ℤ → ℂ)
    (hF : ∀ x : ℤ, x < 0 ∨ (J : ℤ) < x → F x = 0) :
    (∑ i ∈ Finset.range (p + 1), F (i : ℤ)) = ∑ᶠ x : ℤ, F x := by
  have hsub : (Function.support fun i : ℕ => F (i : ℤ)) ⊆ ↑(Finset.range (p + 1)) := by
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    exact hi (hF (i : ℤ) (Or.inr (by
      have : (J : ℤ) ≤ (p : ℤ) := by exact_mod_cast hJp
      have : (p : ℤ) < (i : ℤ) := by exact_mod_cast (by omega : p < i)
      omega)))
  rw [← finsum_eq_sum_of_support_subset _ hsub]
  exact finsum_nat_to_int _ F (fun x hx => hF x (Or.inl hx)) (fun _ => rfl)

/-! ## Case 1: the scalar identity `p₁ ≥ 0 > q`. -/

/-- **`la4.8` case 1, coefficientwise**: for `q < 0` and `−q−1 ≤ p₁`,
`∑_{i≤p₁} (−1)ⁱ C(q+i,i)·C(D+q+1, ℓ+q+i+1) = C(D, ℓ)`. -/
theorem la48_c1_coeff (D q : ℤ) (hq : q < 0) (p₁ : ℕ) (hJ : -q - 1 ≤ (p₁ : ℤ)) (ℓ : ℤ) :
    (∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz (q + (i : ℤ)) (i : ℤ) * cbz (D + q + 1) (ℓ + q + (i : ℤ) + 1))
      = cbz D ℓ := by
  set J : ℕ := (-q - 1).toNat with hJdef
  have hqJ : q = -(J : ℤ) - 1 := by
    rw [hJdef, Int.toNat_of_nonneg (by omega)]; ring
  have hJp : J ≤ p₁ := by
    have : (J : ℤ) ≤ (p₁ : ℤ) := by rw [hJdef, Int.toNat_of_nonneg (by omega)]; exact hJ
    exact_mod_cast this
  -- rewrite each term as `C(J,i)·C(D−J, ℓ−J+i)`
  have hterm : ∀ i : ℕ,
      (-1 : ℂ) ^ i * cbz (q + (i : ℤ)) (i : ℤ) * cbz (D + q + 1) (ℓ + q + (i : ℤ) + 1)
        = cbz (J : ℤ) (i : ℤ) * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + (i : ℤ)) := by
    intro i
    rw [alt_cbz_eq, show (-q - 1) = (J : ℤ) from by omega,
      show (D + q + 1) = D - (J : ℤ) from by omega,
      show (ℓ + q + (i : ℤ) + 1) = ℓ - (J : ℤ) + (i : ℤ) from by omega]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  -- to a `ℤ`-finsum
  rw [range_to_intFinsum J p₁ hJp
    (fun x => cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + x))
    (fun x hx => by
      show cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + x) = 0
      rcases hx with hx | hx
      · rw [cbz_apply_neg _ hx, zero_mul]
      · rw [cbz_lt (by positivity) hx, zero_mul])]
  -- reflect `x ↦ J − x` and apply Vandermonde
  have hrefl : (∑ᶠ x : ℤ, cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + x))
      = ∑ᶠ x : ℤ, cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - x) := by
    calc (∑ᶠ x : ℤ, cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + x))
        = ∑ᶠ x : ℤ, (fun y : ℤ => cbz (J : ℤ) y * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + y))
            (Equiv.subLeft (J : ℤ) x) := by
          exact (finsum_comp_equiv (Equiv.subLeft (J : ℤ))
            (f := fun y : ℤ => cbz (J : ℤ) y * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + y))).symm
      _ = ∑ᶠ x : ℤ, cbz (J : ℤ) x * cbz (D - (J : ℤ)) (ℓ - x) := by
          refine finsum_congr fun x => ?_
          show cbz (J : ℤ) ((J : ℤ) - x) * cbz (D - (J : ℤ)) (ℓ - (J : ℤ) + ((J : ℤ) - x)) = _
          rw [← ZhuMu.cbz_symm J x,
            show (ℓ - (J : ℤ) + ((J : ℤ) - x)) = ℓ - x from by ring]
  rw [hrefl]
  have hv := cbz_vandermonde (J : ℤ) (D - (J : ℤ)) ℓ
  rw [cbzConvol] at hv
  rw [hv, show ((J : ℤ) + (D - (J : ℤ))) = D from by ring]

/-! ## Case 2: the scalar identity `p₂ ≥ 0 > r`. -/

/-- **`la4.8` case 2, coefficientwise** (after the residue skew swap): for `r < 0` and
`−r−1 ≤ p₂`,
`∑_{i≤p₂} (−1)ⁱ C(r+i,i)·sgn(r+i+2)·C(D+i, ℓ+r+i+1) = −C(D, ℓ)`. -/
theorem la48_c2_coeff (D r : ℤ) (hr : r < 0) (p₂ : ℕ) (hJ : -r - 1 ≤ (p₂ : ℤ)) (ℓ : ℤ) :
    (∑ i ∈ Finset.range (p₂ + 1),
        (-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) * sgn (r + (i : ℤ) + 2)
          * cbz (D + (i : ℤ)) (ℓ + r + (i : ℤ) + 1))
      = -cbz D ℓ := by
  set J : ℕ := (-r - 1).toNat with hJdef
  have hrJ : r = -(J : ℤ) - 1 := by
    rw [hJdef, Int.toNat_of_nonneg (by omega)]; ring
  have hJp : J ≤ p₂ := by
    have : (J : ℤ) ≤ (p₂ : ℤ) := by rw [hJdef, Int.toNat_of_nonneg (by omega)]; exact hJ
    exact_mod_cast this
  -- `sgn(r+i+2) = sgn r · (−1)ⁱ` and `sgn r = −(−1)^J`
  have hsgnr : sgn r = -((-1 : ℂ) ^ J) := by
    rw [hrJ, show (-(J : ℤ) - 1) = -(((J + 1 : ℕ)) : ℤ) from by push_cast; ring, sgn_neg',
      sgn_natCast, pow_succ]
    ring
  have hterm : ∀ i : ℕ,
      (-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) * sgn (r + (i : ℤ) + 2)
          * cbz (D + (i : ℤ)) (ℓ + r + (i : ℤ) + 1)
        = -((-1 : ℂ) ^ J) *
            (sgn (i : ℤ) * cbz (J : ℤ) (i : ℤ) * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ))) := by
    intro i
    have h1 : sgn (r + (i : ℤ) + 2) = sgn r * (-1 : ℂ) ^ i := by
      rw [show (r + (i : ℤ) + 2) = (r + (i : ℤ)) + 2 from by ring, sgn_add_two, sgn_add,
        sgn_natCast]
    have h2 : (-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) = cbz (J : ℤ) (i : ℤ) := by
      rw [alt_cbz_eq, show (-r - 1) = (J : ℤ) from by omega]
    have h3 : sgn (i : ℤ) = (-1 : ℂ) ^ i := sgn_natCast i
    have h4 : cbz (D + (i : ℤ)) (ℓ + r + (i : ℤ) + 1)
        = cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ)) := by
      rw [show (ℓ + r + (i : ℤ) + 1) = ℓ - (J : ℤ) + (i : ℤ) from by omega]
    rw [h1, h4, hsgnr, h3]
    calc (-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) * (-((-1 : ℂ) ^ J) * (-1 : ℂ) ^ i)
          * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ))
        = -((-1 : ℂ) ^ J) * (-1 : ℂ) ^ i
            * ((-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ))
            * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ)) := by ring
      _ = -((-1 : ℂ) ^ J) * (-1 : ℂ) ^ i * cbz (J : ℤ) (i : ℤ)
            * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ)) := by rw [h2]
      _ = -((-1 : ℂ) ^ J) * ((-1 : ℂ) ^ i * cbz (J : ℤ) (i : ℤ)
            * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ))) := by ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  -- the inner sum: convert to a `ℤ`-finsum, reflect `x ↦ J − x`, apply `cbz_alt_vandermonde`
  have hinner : (∑ i ∈ Finset.range (p₂ + 1),
        sgn (i : ℤ) * cbz (J : ℤ) (i : ℤ) * cbz (D + (i : ℤ)) (ℓ - (J : ℤ) + (i : ℤ)))
      = (-1 : ℂ) ^ J * cbz D ℓ := by
    rw [range_to_intFinsum J p₂ hJp
      (fun x => sgn x * cbz (J : ℤ) x * cbz (D + x) (ℓ - (J : ℤ) + x))
      (fun x hx => by
        show sgn x * cbz (J : ℤ) x * cbz (D + x) (ℓ - (J : ℤ) + x) = 0
        rcases hx with hx | hx
        · rw [cbz_apply_neg (J : ℤ) hx, mul_zero, zero_mul]
        · rw [cbz_lt (by positivity) hx, mul_zero, zero_mul])]
    have hrefl : (∑ᶠ x : ℤ, sgn x * cbz (J : ℤ) x * cbz (D + x) (ℓ - (J : ℤ) + x))
        = ∑ᶠ x : ℤ, ((-1 : ℂ) ^ J) *
            (sgn x * cbz (J : ℤ) x * cbz ((D + (J : ℤ)) - x) (ℓ - x)) := by
      calc (∑ᶠ x : ℤ, sgn x * cbz (J : ℤ) x * cbz (D + x) (ℓ - (J : ℤ) + x))
          = ∑ᶠ x : ℤ, (fun y : ℤ => sgn y * cbz (J : ℤ) y * cbz (D + y) (ℓ - (J : ℤ) + y))
              (Equiv.subLeft (J : ℤ) x) :=
            (finsum_comp_equiv (Equiv.subLeft (J : ℤ))
              (f := fun y : ℤ => sgn y * cbz (J : ℤ) y * cbz (D + y) (ℓ - (J : ℤ) + y))).symm
        _ = ∑ᶠ x : ℤ, ((-1 : ℂ) ^ J) *
              (sgn x * cbz (J : ℤ) x * cbz ((D + (J : ℤ)) - x) (ℓ - x)) := by
            refine finsum_congr fun x => ?_
            show sgn ((J : ℤ) - x) * cbz (J : ℤ) ((J : ℤ) - x)
                * cbz (D + ((J : ℤ) - x)) (ℓ - (J : ℤ) + ((J : ℤ) - x)) = _
            rw [← ZhuMu.cbz_symm J x,
              show (D + ((J : ℤ) - x)) = (D + (J : ℤ)) - x from by ring,
              show (ℓ - (J : ℤ) + ((J : ℤ) - x)) = ℓ - x from by ring,
              show ((J : ℤ) - x) = (J : ℤ) + (-x) from by ring, sgn_add, sgn_neg', sgn_natCast]
            ring
    have hpull : (∑ᶠ x : ℤ,
          ((-1 : ℂ) ^ J) * (sgn x * cbz (J : ℤ) x * cbz ((D + (J : ℤ)) - x) (ℓ - x)))
        = ((-1 : ℂ) ^ J)
            * ∑ᶠ x : ℤ, (sgn x * cbz (J : ℤ) x * cbz ((D + (J : ℤ)) - x) (ℓ - x)) := by
      have h := smul_finsum' ((-1 : ℂ) ^ J)
        (cbzAltVan_support_finite (J : ℤ) (D + (J : ℤ)) ℓ)
      simp only [smul_eq_mul] at h
      exact h.symm
    rw [hrefl, hpull, cbz_alt_vandermonde J (D + (J : ℤ)) ℓ,
      show ((D + (J : ℤ)) - (J : ℤ)) = D from by ring]
  rw [hinner]
  have hsq : ((-1 : ℂ) ^ J) * ((-1 : ℂ) ^ J) = 1 := by
    rw [← pow_add, show J + J = 2 * J from by ring, pow_mul]; norm_num
  calc -((-1 : ℂ) ^ J) * ((-1 : ℂ) ^ J * cbz D ℓ)
      = -(((-1 : ℂ) ^ J) * ((-1 : ℂ) ^ J)) * cbz D ℓ := by ring
    _ = -cbz D ℓ := by rw [hsq]; ring

/-! ## The residue-level boundary lemmas (DJ `la4.8`). -/

/-- **DJ `la4.8`, case 1** (`p₂ = m+N−p₁ < 0 ≤ p₁`): `a ∗^N_{m,p₁} b = Res_z (1+z)^{wt a−1+p₁−N} Y(a,z)b`.

Note this is an **exact equality in `𝒱`**, not merely a congruence: after `cbz_neg_upper` the
alternating binomial is already complete, so no `O'`-truncation step is needed. -/
theorem dj48_case1 (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (b : 𝒱) (m p₁ N : ℕ)
    (hlt : (N : ℤ) + (m : ℤ) < (p₁ : ℤ)) :
    anmGen W N m p₁ a b = resExp W ((K : ℤ) - 1 + (p₁ : ℤ) - (N : ℤ)) a b := by
  set q : ℤ := (m : ℤ) + (N : ℤ) - (p₁ : ℤ) with hq
  set D : ℤ := (K : ℤ) - 1 + (p₁ : ℤ) - (N : ℤ) with hD
  have hqneg : q < 0 := by rw [hq]; omega
  have hJ : -q - 1 ≤ (p₁ : ℤ) := by rw [hq]; omega
  have hKm : ((K : ℤ) + (m : ℤ)) = D + q + 1 := by rw [hD, hq]; ring
  -- both sides as `resFull` combinations
  have hLHS : anmGen W N m p₁ a b
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz (q + (i : ℤ)) (i : ℤ)) •
            resFull W ((K : ℤ) + (m : ℤ)) (q + (i : ℤ) + 1) a b := by
    rw [anmGen]
    exact Finset.sum_congr rfl fun i _ => by rw [resHom_eq_resFull W ha _ b]
  rw [hLHS, finsetSum_smul_resFull W _ _ _ _ a b, resExp_eq_resFull, resFull]
  refine finsum_congr fun ℓ => ?_
  congr 1
  rw [show (ℓ + 0 : ℤ) = ℓ from by ring, ← la48_c1_coeff D q hqneg p₁ hJ ℓ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hKm, show (ℓ + (q + (i : ℤ) + 1)) = ℓ + q + (i : ℤ) + 1 from by ring]

/-- **DJ `la4.8`, case 2** (`p₁ = m+N−p₂ < 0 ≤ p₂`):
`−(b ∗^N_{m,p₂} a) ≡ Res_z (1+z)^{wt a−1+m−p₂} Y(a,z)b (mod O'_{N,m})`.

Here the `O'` really is needed — it enters through `resHom_skew_mod_Onm`, which swaps the two
arguments of each residue. -/
theorem dj48_case2 (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a b : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hb : b ∈ W.grading (M : ℤ)) (m p₂ N : ℕ)
    (hlt : (N : ℤ) + (m : ℤ) < (p₂ : ℤ)) :
    -anmGen W N m p₂ b a - resExp W ((K : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ)) a b ∈ Onm W N m := by
  set r : ℤ := (m : ℤ) + (N : ℤ) - (p₂ : ℤ) with hr
  set D : ℤ := (K : ℤ) - 1 + (m : ℤ) - (p₂ : ℤ) with hD
  have hrneg : r < 0 := by rw [hr]; omega
  have hJ : -r - 1 ≤ (p₂ : ℤ) := by rw [hr]; omega
  -- swap each residue by the skew relation
  have hswap : anmGen W N m p₂ b a
      - ∑ i ∈ Finset.range (p₂ + 1),
          ((-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) * sgn (r + (i : ℤ) + 2)) •
            resFull W (D + (i : ℤ)) (r + (i : ℤ) + 1) a b ∈ Onm W N m := by
    rw [anmGen, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsk := Submodule.smul_mem (Onm W N m)
      ((-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ))
      (resHom_skew_mod_Onm W N m ha hb (r + (i : ℤ) + 1))
    rw [smul_sub, smul_smul] at hsk
    have hexp : ((K : ℤ) + (r + (i : ℤ) + 1) - (N : ℤ) - 2) = D + (i : ℤ) := by
      rw [hD, hr]; ring
    have hpole : ((m : ℤ) + (N : ℤ) - (p₂ : ℤ) + (i : ℤ) + 1) = r + (i : ℤ) + 1 := by rw [hr]
    rw [hexp] at hsk
    have hsgnarg : (r + (i : ℤ) + 1 + 1) = r + (i : ℤ) + 2 := by ring
    rw [hsgnarg] at hsk
    exact hsk
  -- the swapped combination is exactly `−resExp`
  have hval : (∑ i ∈ Finset.range (p₂ + 1),
        ((-1 : ℂ) ^ i * cbz (r + (i : ℤ)) (i : ℤ) * sgn (r + (i : ℤ) + 2)) •
          resFull W (D + (i : ℤ)) (r + (i : ℤ) + 1) a b)
      = -resExp W D a b := by
    rw [finsetSum_smul_resFull W _ _ _ _ a b, resExp_eq_resFull, resFull]
    rw [← finsum_neg_distrib]
    refine finsum_congr fun ℓ => ?_
    rw [← neg_smul]
    congr 1
    rw [show (ℓ + 0 : ℤ) = ℓ from by ring, ← la48_c2_coeff D r hrneg p₂ hJ ℓ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (ℓ + (r + (i : ℤ) + 1)) = ℓ + r + (i : ℤ) + 1 from by ring]
  rw [hval] at hswap
  have : -anmGen W N m p₂ b a - resExp W D a b
      = -(anmGen W N m p₂ b a - -resExp W D a b) := by abel
  rw [this]
  exact (Onm W N m).neg_mem hswap

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.cbz_neg_upper
  #print axioms VOA.la48_c1_coeff
  #print axioms VOA.la48_c2_coeff
  #print axioms VOA.dj48_case1
  #print axioms VOA.dj48_case2
-/
