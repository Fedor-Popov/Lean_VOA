/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedBase

/-!
# The leading coefficient of the twisted product of two exponentials  (Moonshine step M6)

The vacuum expectation of the leading twisted product `star (e/2) F_e(e^α) (−⟨α,β⟩−1) F_{e'}(e^β)`,
summed over the two classes, is a finite combination of the coefficients `fco(n)` of
`((1−y)/(1+y))ⁿ` (`n = ⟨α,β⟩`).  This file evaluates it:

  `Σ_{e ∈ {0,1}} Σ_i C(−e/2, i) V_e(−n−1+i) = 4^{−n}`   (`leading_plus`),
  `Σ_{e ∈ {0,1}} (−1)ᵉ Σ_i C(−e/2, i) V_e(n−1+i) = 4ⁿ`   (`leading_minus`),

which is exactly the normalization `2^{−⟨α,α⟩}` of `Y^T(e^α)` (`2^{−|α|²−|β|²}·4^{−n} = 2^{−|α+β|²}`).

## Method
* `taylor` — **the Taylor formula** for the class-`e` two-point function: with
  `G(y) = (1−y)^{K+n}(1+y)^{K−n}` (`K = |n|`, `gz`),
  `V(r', Q) = Σ_{u ≡ r'} g_u C((2K−2−r'−u)/2, K−Q−1)`.  Proof: `(1−y²)^Q φ = (1−y²)^{Q−K} G`
  (`convA`, Vandermonde), the palindromy of `G`, and a binomial identity (`tau_eq`).
* The star sum is a Vandermonde convolution; the two classes recombine the two parities of `u`.
* `sum_gz_cbinom` — `Σ_u g_u C((M−u)/2, a) = 2^{b−a}`, by the power series
  `B(c) = Σ C(c,j) tʲ = (1+t)ᶜ` (`bs`, `bs_mul`): the sum is the coefficient of `t^a` in
  `B(M/2)·G(B(−1/2))`, and `1 − B(−1/2) = t·W` with `W(0) = ½`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open TwistedReduction PowerSeries
open scoped BigOperators

/-! ## The binomial power series -/

/-- `B(c) = Σ_j C(c, j) tʲ = (1+t)ᶜ`. -/
noncomputable def bs (c : ℂ) : ℂ⟦X⟧ := PowerSeries.mk (cbinom c)

@[simp] theorem coeff_bs (c : ℂ) (j : ℕ) : coeff j (bs c) = cbinom c j := by
  rw [bs, coeff_mk]

theorem bs_mul (c d : ℂ) : bs c * bs d = bs (c + d) := by
  ext j
  rw [coeff_mul, coeff_bs, ← gBinom_vandermonde]
  simp only [coeff_bs]

theorem bs_zero : bs 0 = 1 := by
  ext j
  rw [coeff_bs, cbinom_zero_left, coeff_one]

theorem bs_pow (c : ℂ) (u : ℕ) : bs c ^ u = bs (u * c) := by
  induction u with
  | zero => simp [bs_zero]
  | succ u ih => rw [pow_succ, ih, bs_mul]; push_cast; ring_nf

theorem constantCoeff_bs (c : ℂ) : constantCoeff (bs c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bs, cbinom_zero]

/-- `1 − B(−½) = t · W`. -/
noncomputable def Wser : ℂ⟦X⟧ := PowerSeries.mk fun j => -cbinom (-1 / 2) (j + 1)

theorem one_sub_bs_half : 1 - bs (-1 / 2) = X * Wser := by
  ext j
  rcases j with _ | j
  · rw [map_sub, coeff_one, if_pos rfl, coeff_bs, cbinom_zero, sub_self, coeff_zero_X_mul]
  · rw [map_sub, coeff_one, if_neg (by omega), coeff_bs, coeff_succ_X_mul, Wser, coeff_mk]
    ring

theorem constantCoeff_Wser : constantCoeff Wser = 1 / 2 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Wser, coeff_mk]
  simp [cbinom]
  norm_num

/-- **The power-series evaluation**: `Σ_u g_u C((M−u)/2, a) = 2^{b−a}` for
`G = (1−y)ᵃ(1+y)ᵇ`. -/
theorem sum_gz_cbinom (a b : ℕ) (M : ℤ) :
    ∑ u ∈ Finset.range (a + b + 1), gz a b u * cbinom (((M : ℂ) - u) / 2) a
      = (1 / 2 : ℂ) ^ a * 2 ^ b := by
  -- the sum is a coefficient of `B(M/2) · G(B(−½))`
  have hterm : ∀ u : ℕ, cbinom (((M : ℂ) - u) / 2) a
      = coeff a (bs ((M : ℂ) / 2) * bs (-1 / 2) ^ u) := by
    intro u
    rw [bs_pow, bs_mul, coeff_bs]
    congr 1
    ring
  have hG : ∑ u ∈ Finset.range (a + b + 1), gz a b u • bs (-1 / 2) ^ u
      = (1 - bs (-1 / 2)) ^ a * (1 + bs (-1 / 2)) ^ b := by
    have h1 : Polynomial.aeval (bs (-1 / 2)) (gpoly a b)
        = (1 - bs (-1 / 2)) ^ a * (1 + bs (-1 / 2)) ^ b := by
      simp [gpoly]
    rw [← h1, Polynomial.aeval_eq_sum_range' (n := a + b + 1)
      (Nat.lt_succ_of_le (natDegree_gpoly_le a b))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gz, if_pos (by omega), Int.toNat_natCast]
  calc ∑ u ∈ Finset.range (a + b + 1), gz a b u * cbinom (((M : ℂ) - u) / 2) a
      = coeff a (bs ((M : ℂ) / 2) * ∑ u ∈ Finset.range (a + b + 1), gz a b u • bs (-1 / 2) ^ u) := by
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hterm, mul_smul_comm, LinearMap.map_smul_of_tower, smul_eq_mul]
    _ = coeff a (X ^ a * (bs ((M : ℂ) / 2) * Wser ^ a * (1 + bs (-1 / 2)) ^ b)) := by
        rw [hG, one_sub_bs_half, mul_pow]
        congr 1
        ring
    _ = (1 / 2 : ℂ) ^ a * 2 ^ b := by
        rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
        simp only [map_mul, map_pow, map_add, map_one, constantCoeff_bs, constantCoeff_Wser]
        norm_num

/-! ## `(1−y²)^Q φ = (1−y²)^{Q−K} G` -/

theorem fz_neg (n : ℂ) {t : ℤ} (ht : t < 0) : fz n t = 0 := by rw [fz, if_neg (by omega)]

theorem gz_neg (a b : ℕ) {t : ℤ} (ht : t < 0) : gz a b t = 0 := by rw [gz, if_neg (by omega)]

theorem gz_big (a b : ℕ) {t : ℤ} (ht : ((a + b : ℕ) : ℤ) < t) : gz a b t = 0 := by
  rw [gz, if_pos (by omega)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_gpoly_le a b).trans_lt (by omega))

/-- **`(1−y²)^Q φ = (1−y²)^{Q−K} G`**, coefficientwise (`K ≥ |n|`). -/
theorem convA (n : ℤ) (K : ℕ) (h1 : -(K : ℤ) ≤ n) (h2 : n ≤ K) (Q t : ℤ) (J : ℕ)
    (hJ : t < 2 * J) :
    ∑ j ∈ Finset.range J, ((-1 : ℂ) ^ j * gBinom Q j) * fz n (t - 2 * j)
      = ∑ j ∈ Finset.range J, ((-1 : ℂ) ^ j * gBinom (Q - K) j)
          * gz (K + n).toNat (K - n).toNat (t - 2 * j) := by
  set L : ℕ := J + K + 1 with hL
  have hfz : ∀ s : ℕ, J ≤ s → fz (n : ℂ) (t - 2 * s) = 0 := fun s hs => fz_neg _ (by omega)
  -- expand `G` through the defining relation
  have hG : ∀ j : ℕ, gz (K + n).toNat (K - n).toNat (t - 2 * j)
      = ∑ k ∈ Finset.range L, ((-1 : ℂ) ^ k * cbinom (K : ℂ) k) * fz n (t - 2 * (j + k : ℕ)) := by
    intro j
    rw [Finset.sum_range_eq_of_vanish' (K + 1) L (by omega) (fun k _ hk => by
      rw [cbinom_natCast_of_lt (by omega), mul_zero, zero_mul]),
      ← sum_binom_fz_eq_gz K n h1 h2 (t - 2 * j), ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show K + 1 - 1 - k = K - k by omega, show K - (K - k) = k by omega,
      Nat.choose_symm (by omega : k ≤ K), cbinom_natCast]
    congr 1
    push_cast [Nat.cast_sub (show k ≤ K by omega)]
    ring_nf
  simp only [hG, Finset.mul_sum]
  rw [← Finset.sum_range_eq_of_vanish' J L (by omega) (fun j _ hj => by
      rw [hfz j hj, mul_zero]),
    ← Finset.sum_range_eq_of_vanish' J L (by omega) (fun j _ hj =>
      Finset.sum_eq_zero fun k _ => by
        rw [show t - 2 * ((j + k : ℕ) : ℤ) = t - 2 * ((j + k : ℕ) : ℤ) from rfl,
          hfz (j + k) (by omega), mul_zero, mul_zero])]
  rw [sum_range_sq_eq_sum_antidiagonal L _ (fun j k h => by
    rw [hfz (j + k) (by omega), mul_zero, mul_zero])]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hV := gBinom_vandermonde ((Q - K : ℤ) : ℂ) (K : ℂ) s
  rw [show ((Q - K : ℤ) : ℂ) + (K : ℂ) = (Q : ℂ) by push_cast; ring] at hV
  rw [show gBinom Q s = cbinom (Q : ℂ) s from rfl, ← hV, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, show gBinom (Q - K) p.1 = cbinom ((Q - K : ℤ) : ℂ) p.1 from rfl, pow_add]
  ring_nf

/-! ## Binomial identities -/

/-- Upper negation: `C(−x, k) = (−1)ᵏ C(x+k−1, k)`. -/
theorem cbinom_neg (x : ℂ) (k : ℕ) : cbinom (-x) k = (-1 : ℂ) ^ k * cbinom (x + k - 1) k := by
  have h1 : ∏ i ∈ Finset.range k, (x + k - 1 - i) = ∏ i ∈ Finset.range k, (x + i) := by
    rw [← Finset.prod_range_reflect (fun i : ℕ => x + i) k]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : ((k - 1 - i : ℕ) : ℂ) = (k : ℂ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; ring
  have h2 : ∏ i ∈ Finset.range k, (-x - i) = (-1 : ℂ) ^ k * ∏ i ∈ Finset.range k, (x + i) := by
    rw [Finset.pow_eq_prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [cbinom, cbinom, h1, h2, mul_div_assoc]

theorem cbinom_symm_nat (N k : ℕ) (h : k ≤ N) : cbinom (N : ℂ) k = cbinom (N : ℂ) (N - k) := by
  rw [cbinom_natCast, cbinom_natCast, Nat.choose_symm h]

theorem neg_one_zpow_of_nonneg {v : ℤ} (hv : 0 ≤ v) : (-1 : ℂ) ^ v = (-1 : ℂ) ^ v.toNat := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hv]

theorem cbinom_int_nonneg {N : ℤ} (hN : 0 ≤ N) (k : ℕ) : cbinom (N : ℂ) k = cbinom ((N.toNat : ℕ) : ℂ) k := by
  rw [show ((N.toNat : ℕ) : ℂ) = ((N.toNat : ℤ) : ℂ) by norm_cast, Int.toNat_of_nonneg hN]

/-- **The binomial identity behind the Taylor formula**:
`[v≥0](−1)ᵛ C(P,v) − (−1)ᴾ [v≤P] (−1)^{P−v} C(P,P−v) = [P<0] C(v−P−1, −P−1)`. -/
theorem tau_eq (P v : ℤ) :
    (if 0 ≤ v then (-1 : ℂ) ^ v * cbinom (P : ℂ) v.toNat else 0)
      - (-1 : ℂ) ^ P * (if 0 ≤ P - v then (-1 : ℂ) ^ (P - v) * cbinom (P : ℂ) (P - v).toNat else 0)
      = if P < 0 then cbinom ((v - P - 1 : ℤ) : ℂ) (-P - 1).toNat else 0 := by
  rcases le_or_gt 0 P with hP | hP
  · -- `P ≥ 0`: the two terms cancel
    rw [if_neg (show ¬ P < 0 by omega)]
    rw [cbinom_int_nonneg hP, cbinom_int_nonneg hP]
    by_cases hv0 : 0 ≤ v
    · by_cases hvp : v ≤ P
      · rw [if_pos hv0, if_pos (show 0 ≤ P - v by omega), neg_one_zpow_of_nonneg hv0,
          neg_one_zpow_of_nonneg hP, neg_one_zpow_of_nonneg (show (0 : ℤ) ≤ P - v by omega),
          cbinom_symm_nat P.toNat v.toNat (by omega),
          show P.toNat - v.toNat = (P - v).toNat by omega, ← mul_assoc, ← pow_add,
          show P.toNat + (P - v).toNat = v.toNat + 2 * (P - v).toNat by omega,
          pow_add, pow_mul]
        simp
      · rw [if_pos hv0, if_neg (show ¬ 0 ≤ P - v by omega),
          cbinom_natCast_of_lt (show P.toNat < v.toNat by omega)]
        simp
    · rw [if_neg hv0, if_pos (show 0 ≤ P - v by omega),
        cbinom_natCast_of_lt (show P.toNat < (P - v).toNat by omega)]
      simp
  · -- `P < 0`: write `P = −m`
    rw [if_pos hP]
    obtain ⟨m, hm, rfl⟩ : ∃ m : ℕ, 1 ≤ m ∧ P = -(m : ℤ) := ⟨(-P).toNat, by omega, by omega⟩
    have hneg : ∀ k : ℕ, cbinom ((-(m : ℤ) : ℤ) : ℂ) k
        = (-1 : ℂ) ^ k * cbinom ((m + k - 1 : ℕ) : ℂ) k := by
      intro k
      rw [show ((-(m : ℤ) : ℤ) : ℂ) = -(m : ℂ) by push_cast; ring, cbinom_neg]
      congr 2
      push_cast [Nat.cast_sub (show 1 ≤ m + k by omega)]
      ring
    rw [show (-(-(m : ℤ)) - 1).toNat = m - 1 by omega]
    rcases le_or_gt 0 v with hv0 | hv0
    · -- `v ≥ 0`: only the first term
      obtain ⟨vn, rfl⟩ : ∃ vn : ℕ, v = vn := ⟨v.toNat, by omega⟩
      rw [if_pos hv0, if_neg (show ¬ 0 ≤ -(m : ℤ) - vn by omega), mul_zero, sub_zero, hneg,
        ← mul_assoc, Int.toNat_natCast, zpow_natCast, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
        one_pow, one_mul,
        show (((vn : ℤ) - -(m : ℤ) - 1 : ℤ) : ℂ) = ((m + vn - 1 : ℕ) : ℂ) by
          push_cast [Nat.cast_sub (show 1 ≤ m + vn by omega)]; ring,
        cbinom_symm_nat _ _ (by omega), show m + vn - 1 - vn = m - 1 by omega]
    · rcases le_or_gt v (-(m : ℤ)) with hvm | hvm
      · -- `v ≤ −m`: only the second term
        rw [if_neg (show ¬ 0 ≤ v by omega), zero_sub, if_pos (show 0 ≤ -(m : ℤ) - v by omega), hneg]
        obtain ⟨k, hk⟩ : ∃ k : ℕ, -(m : ℤ) - v = k := ⟨(-(m : ℤ) - v).toNat, by omega⟩
        rw [hk, Int.toNat_natCast, show m + k - 1 = (m - 1) + k by omega,
          cbinom_symm_nat _ _ (by omega), show m - 1 + k - k = m - 1 by omega]
        -- the target: `C(v + m − 1, m − 1)` with negative upper index
        have ht : ((v - -(m : ℤ) - 1 : ℤ) : ℂ) = -((k : ℂ) + 1) := by
          have : v = -(m : ℤ) - k := by omega
          rw [this]; push_cast; ring
        rw [ht, cbinom_neg, show (k : ℂ) + 1 + ((m - 1 : ℕ) : ℂ) - 1 = ((m - 1 + k : ℕ) : ℂ) by
          push_cast; ring, zpow_natCast]
        have hm1 : (-1 : ℂ) ^ (m - 1) = -(-1 : ℂ) ^ m := by
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ]; ring
        rw [hm1, zpow_neg, zpow_natCast]
        have hsq : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by
          rw [← inv_pow, inv_neg, inv_one]
        rw [hsq, ← mul_assoc, ← pow_add]
        rw [← mul_assoc, ← pow_add, show m + k + k = m + 2 * k by ring, pow_add, pow_mul,
          neg_one_sq, one_pow, mul_one]
        ring
      · -- `−m < v < 0`: both sides vanish
        rw [if_neg (show ¬ 0 ≤ v by omega), if_neg (show ¬ 0 ≤ -(m : ℤ) - v by omega), mul_zero,
          sub_zero]
        obtain ⟨w, hw⟩ : ∃ w : ℕ, v - -(m : ℤ) - 1 = w := ⟨(v + m - 1).toNat, by omega⟩
        rw [hw, Int.cast_natCast, cbinom_natCast_of_lt (by omega)]

/-! ## The Taylor formula -/

/-- Reindexing `Σ_j c_j h(w − 2j)` by `u = w − 2j`, for `h` supported in `[0, D]`. -/
theorem sum_reindex_two (h : ℤ → ℂ) (D : ℕ) (hh : ∀ t : ℤ, (t < 0 ∨ (D : ℤ) < t) → h t = 0)
    (c : ℕ → ℂ) (w : ℤ) (J : ℕ) (hJ : w < 2 * J) :
    ∑ j ∈ Finset.range J, c j * h (w - 2 * j)
      = ∑ u ∈ Finset.range (D + 1), h u *
          (if (w - u) % 2 = 0 ∧ 0 ≤ w - u then c ((w - u) / 2).toNat else 0) := by
  have hin : ∀ u : ℕ, (if (w - u) % 2 = 0 ∧ 0 ≤ w - u then c ((w - u) / 2).toNat else 0)
      = ∑ j ∈ Finset.range J, if w - 2 * j = u then c j else 0 := by
    intro u
    split_ifs with hc
    · rw [Finset.sum_eq_single ((w - u) / 2).toNat (fun j _ hj => by
        rw [if_neg (by omega)]) (fun hj => absurd (Finset.mem_range.mpr (by omega)) hj),
        if_pos (by omega)]
    · exact (Finset.sum_eq_zero fun j _ => by rw [if_neg (by omega)]).symm
  simp only [hin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hr : 0 ≤ w - 2 * j ∧ w - 2 * j ≤ D
  · rw [Finset.sum_eq_single (w - 2 * j).toNat (fun u _ hu => by
      rw [if_neg (by omega), mul_zero]) (fun hu => absurd (Finset.mem_range.mpr (by omega)) hu),
      if_pos (by omega), Int.toNat_of_nonneg hr.1, mul_comm]
  · rw [hh _ (by omega), mul_zero]
    refine (Finset.sum_eq_zero fun u hu => ?_).symm
    rw [Finset.mem_range] at hu
    rw [if_neg (by omega), mul_zero]

/-- **The Taylor formula** for the class-`e` two-point coefficients:
`Σ_j (−1)ʲ C(Q,j) [φ_{2Q−2j−r'} − (−1)^{Q+n} φ_{r'−2j}]
   = Σ_{u ≡ r'} g_u C((2K−2−r'−u)/2, K−Q−1)`. -/
theorem taylor (n r' Q : ℤ) (J : ℕ) (hJ1 : 2 * Q - r' < 2 * J) (hJ2 : r' < 2 * J) :
    ∑ j ∈ Finset.range J, ((-1 : ℂ) ^ j * gBinom Q j)
        * (fz n (2 * Q - 2 * j - r') - (-1 : ℂ) ^ (Q + n) * fz n (r' - 2 * j))
      = ∑ u ∈ Finset.range (2 * n.natAbs + 1),
          gz (n.natAbs + n).toNat (n.natAbs - n).toNat u
            * (if (u - r') % 2 = 0 ∧ Q < n.natAbs then
                cbinom (((2 * n.natAbs - 2 - r' - u) / 2 : ℤ) : ℂ) (n.natAbs - Q - 1).toNat
              else 0) := by
  set K : ℕ := n.natAbs with hK
  set a : ℕ := (K + n).toNat with ha
  set b : ℕ := (K - n).toNat with hb
  have hab : a + b = 2 * K := by omega
  have hsupp : ∀ t : ℤ, (t < 0 ∨ ((2 * K : ℕ) : ℤ) < t) → gz a b t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · exact gz_neg a b ht
    · exact gz_big a b (by rw [hab]; exact ht)
  set c' : ℕ → ℂ := fun j => (-1 : ℂ) ^ j * gBinom (Q - K) j with hc'
  -- split the two sums and pass to `G`
  have hA1 := convA n K (by omega) (by omega) Q (2 * Q - r') J hJ1
  have hA2 := convA n K (by omega) (by omega) Q r' J hJ2
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [show ∑ j ∈ Finset.range J, (-1 : ℂ) ^ j * gBinom Q j * fz n (2 * Q - 2 * j - r')
      = ∑ j ∈ Finset.range J, (-1 : ℂ) ^ j * gBinom Q j * fz n (2 * Q - r' - 2 * j) from
      Finset.sum_congr rfl fun j _ => by rw [show 2 * Q - 2 * (j : ℤ) - r' = 2 * Q - r' - 2 * j by
        ring], hA1]
  rw [show ∑ j ∈ Finset.range J, (-1 : ℂ) ^ j * gBinom Q j * ((-1 : ℂ) ^ (Q + n) * fz n (r' - 2 * j))
      = (-1 : ℂ) ^ (Q + n) * ∑ j ∈ Finset.range J, (-1 : ℂ) ^ j * gBinom Q j * fz n (r' - 2 * j) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hA2]
  -- reindex by `u`
  rw [sum_reindex_two (gz a b) (2 * K) hsupp c' (2 * Q - r') J hJ1,
    sum_reindex_two (gz a b) (2 * K) hsupp c' r' J hJ2]
  -- reflect the second sum through the palindromy of `G`
  have h2 : ∑ u ∈ Finset.range (2 * K + 1), gz a b u *
        (if (r' - u) % 2 = 0 ∧ 0 ≤ r' - u then c' ((r' - u) / 2).toNat else 0)
      = ∑ u ∈ Finset.range (2 * K + 1), (-1 : ℂ) ^ a * gz a b u *
        (if (r' - (2 * K - u)) % 2 = 0 ∧ 0 ≤ r' - (2 * K - u) then
          c' ((r' - (2 * K - u)) / 2).toNat else 0) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_range] at hu
    have e1 : ((2 * K + 1 - 1 - u : ℕ) : ℤ) = 2 * K - u := by
      push_cast [Nat.cast_sub (show u ≤ 2 * K by omega)]; ring
    rw [e1, ← gz_palindrome a b u, show ((a + b : ℕ) : ℤ) - u = 2 * K - u by
      push_cast [hab]; ring]
  rw [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  -- the per-`u` identity
  by_cases hpar : (u - r') % 2 = 0
  · set v : ℤ := (2 * Q - r' - u) / 2 with hv
    have hv2 : 2 * Q - r' - u = 2 * v := by omega
    have ht := tau_eq ((Q - K : ℤ)) v
    have hsign : (-1 : ℂ) ^ (Q + n) * (-1 : ℂ) ^ a = (-1 : ℂ) ^ (Q - K) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      exact neg_one_zpow_congr (by rw [ha]; omega)
    have hX1 : (if (2 * Q - r' - u) % 2 = 0 ∧ 0 ≤ 2 * Q - r' - u then
          c' ((2 * Q - r' - u) / 2).toNat else 0)
        = if 0 ≤ v then (-1 : ℂ) ^ v * cbinom ((Q - K : ℤ) : ℂ) v.toNat else 0 := by
      by_cases hv0 : 0 ≤ v
      · rw [if_pos ⟨by omega, by omega⟩, if_pos hv0, ← hv, hc', neg_one_zpow_of_nonneg hv0]
        rfl
      · rw [if_neg (by omega), if_neg hv0]
    have hX2 : (if (r' - (2 * K - u)) % 2 = 0 ∧ 0 ≤ r' - (2 * K - u) then
          c' ((r' - (2 * K - u)) / 2).toNat else 0)
        = if 0 ≤ (Q - K) - v then (-1 : ℂ) ^ ((Q - K) - v) * cbinom ((Q - K : ℤ) : ℂ)
            ((Q - K) - v).toNat else 0 := by
      have e2 : (r' - (2 * K - u)) / 2 = (Q - K) - v := by omega
      by_cases hw0 : 0 ≤ (Q - K) - v
      · rw [if_pos ⟨by omega, by omega⟩, if_pos hw0, e2, hc', neg_one_zpow_of_nonneg hw0]
        rfl
      · rw [if_neg (by omega), if_neg hw0]
    rw [hX1, hX2, show gz a b u * (if 0 ≤ v then (-1 : ℂ) ^ v * cbinom ((Q - K : ℤ) : ℂ) v.toNat
        else 0) - (-1 : ℂ) ^ (Q + n) * ((-1 : ℂ) ^ a * gz a b u * (if 0 ≤ (Q - K) - v then
          (-1 : ℂ) ^ ((Q - K) - v) * cbinom ((Q - K : ℤ) : ℂ) ((Q - K) - v).toNat else 0))
        = gz a b u * ((if 0 ≤ v then (-1 : ℂ) ^ v * cbinom ((Q - K : ℤ) : ℂ) v.toNat else 0)
          - ((-1 : ℂ) ^ (Q + n) * (-1 : ℂ) ^ a) * (if 0 ≤ (Q - K) - v then
            (-1 : ℂ) ^ ((Q - K) - v) * cbinom ((Q - K : ℤ) : ℂ) ((Q - K) - v).toNat else 0)) by
        ring, hsign, ht]
    congr 1
    by_cases hQK : Q < K
    · rw [if_pos (show Q - K < 0 by omega), if_pos ⟨hpar, hQK⟩,
        show v - (Q - K) - 1 = (2 * K - 2 - r' - u) / 2 by omega,
        show (-(Q - K) - 1) = (K - Q - 1) by ring]
    · rw [if_neg (show ¬ Q - K < 0 by omega), if_neg (by tauto)]
  · have h1' : ¬ ((2 * Q - r' - u) % 2 = 0 ∧ 0 ≤ 2 * Q - r' - u) := by omega
    have h2' : ¬ ((r' - (2 * K - u)) % 2 = 0 ∧ 0 ≤ r' - (2 * K - u)) := by omega
    rw [if_neg h1', if_neg h2', if_neg (by tauto)]
    ring

/-! ## The two leading coefficients -/

/-- The class-`e` vacuum coefficient of the `Q`-th product of two twisted exponentials. -/
noncomputable def Vf (n r' Q : ℤ) : ℂ :=
  ∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * gBinom Q j)
    * (fz n (2 * Q - 2 * j - r') - (-1 : ℂ) ^ (Q + n) * fz n (r' - 2 * j))

theorem Vf_eq_range (n r' Q : ℤ) (J : ℕ) (hJ1 : 2 * Q - r' < 2 * J) (hJ2 : r' < 2 * J) :
    Vf n r' Q = ∑ j ∈ Finset.range J, ((-1 : ℂ) ^ j * gBinom Q j)
      * (fz n (2 * Q - 2 * j - r') - (-1 : ℂ) ^ (Q + n) * fz n (r' - 2 * j)) := by
  rw [Vf]
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hj (by rw [fz_neg _ (by omega), fz_neg _ (by omega)]; ring)

/-- **The Taylor formula**, `finsum` form. -/
theorem Vf_taylor (n r' Q : ℤ) :
    Vf n r' Q = ∑ u ∈ Finset.range (2 * n.natAbs + 1),
          gz (n.natAbs + n).toNat (n.natAbs - n).toNat u
            * (if (u - r') % 2 = 0 ∧ Q < n.natAbs then
                cbinom (((2 * n.natAbs - 2 - r' - u) / 2 : ℤ) : ℂ) (n.natAbs - Q - 1).toNat
              else 0) := by
  set J : ℕ := (2 * Q - r').natAbs + r'.natAbs + 1
  rw [Vf_eq_range n r' Q J (by omega) (by omega), taylor n r' Q J (by omega) (by omega)]

/-- The star sum of one class: a Vandermonde convolution of the Taylor formula. -/
theorem star_sum_Vf (n r' q : ℤ) (x : ℂ) (I : ℕ) (hI : n.natAbs - q ≤ I) :
    ∑ i ∈ Finset.range I, cbinom x i * Vf n r' (q + i)
      = ∑ u ∈ Finset.range (2 * n.natAbs + 1),
          gz (n.natAbs + n).toNat (n.natAbs - n).toNat u
            * (if (u - r') % 2 = 0 ∧ q < n.natAbs then
                cbinom ((((2 * n.natAbs - 2 - r' - u) / 2 : ℤ) : ℂ) + x) (n.natAbs - q - 1).toNat
              else 0) := by
  simp only [Vf_taylor, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  set g := gz (n.natAbs + n).toNat (n.natAbs - n).toNat u
  set X0 : ℂ := (((2 * n.natAbs - 2 - r' - u) / 2 : ℤ) : ℂ)
  by_cases hc : (u - r') % 2 = 0 ∧ q < n.natAbs
  · rw [if_pos hc]
    set M : ℕ := (n.natAbs - q - 1).toNat with hM
    have hR : cbinom (X0 + x) M = ∑ i ∈ Finset.range (M + 1), cbinom x i * cbinom X0 (M - i) := by
      rw [add_comm, cbinom_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [hR, Finset.mul_sum, Finset.sum_range_eq_of_vanish' (M + 1) I (by omega)
      (fun i _ hi => by rw [if_neg (by omega), mul_zero, mul_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_pos ⟨hc.1, by omega⟩, show (n.natAbs - (q + i) - 1).toNat = M - i by omega]
    ring
  · rw [if_neg hc, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by omega), mul_zero, mul_zero]

theorem neg_pow_smul (Y : ℂ⟦X⟧) (u : ℕ) : (-Y) ^ u = ((-1 : ℂ) ^ u) • Y ^ u := by
  induction u with
  | zero => simp
  | succ u ih => rw [pow_succ, ih, pow_succ, pow_succ, smul_mul_assoc, mul_neg, smul_neg,
      mul_neg_one, neg_smul]

/-- The power-series evaluation with the alternating sign. -/
theorem sum_gz_cbinom_alt (a b : ℕ) (M : ℤ) :
    ∑ u ∈ Finset.range (a + b + 1), (-1 : ℂ) ^ u * gz a b u * cbinom (((M : ℂ) - u) / 2) b
      = (1 / 2 : ℂ) ^ b * 2 ^ a := by
  have hterm : ∀ u : ℕ, cbinom (((M : ℂ) - u) / 2) b
      = coeff b (bs ((M : ℂ) / 2) * bs (-1 / 2) ^ u) := by
    intro u
    rw [bs_pow, bs_mul, coeff_bs]
    congr 1
    ring
  have hG : ∑ u ∈ Finset.range (a + b + 1), gz a b u • (-bs (-1 / 2)) ^ u
      = (1 + bs (-1 / 2)) ^ a * (1 - bs (-1 / 2)) ^ b := by
    have h1 : Polynomial.aeval (-bs (-1 / 2)) (gpoly a b)
        = (1 + bs (-1 / 2)) ^ a * (1 - bs (-1 / 2)) ^ b := by
      simp [gpoly, sub_eq_add_neg]
    rw [← h1, Polynomial.aeval_eq_sum_range' (n := a + b + 1)
      (Nat.lt_succ_of_le (natDegree_gpoly_le a b))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gz, if_pos (by omega), Int.toNat_natCast]
  calc ∑ u ∈ Finset.range (a + b + 1), (-1 : ℂ) ^ u * gz a b u * cbinom (((M : ℂ) - u) / 2) b
      = coeff b (bs ((M : ℂ) / 2) * ∑ u ∈ Finset.range (a + b + 1), gz a b u • (-bs (-1 / 2)) ^ u) := by
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [neg_pow_smul, hterm, smul_smul, mul_smul_comm, LinearMap.map_smul_of_tower, smul_eq_mul]
        ring
    _ = (1 / 2 : ℂ) ^ b * 2 ^ a := by
        rw [hG, one_sub_bs_half]
        rw [show bs ((M : ℂ) / 2) * ((1 + bs (-1 / 2)) ^ a * (X * Wser) ^ b)
          = X ^ b * (bs ((M : ℂ) / 2) * Wser ^ b * (1 + bs (-1 / 2)) ^ a) by ring]
        rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
        simp only [map_mul, map_pow, map_add, map_one, constantCoeff_bs, constantCoeff_Wser]
        norm_num

theorem cast_half_of_even {z : ℤ} (hz : z % 2 = 0) : ((z / 2 : ℤ) : ℂ) = (z : ℂ) / 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, z = 2 * w := ⟨z / 2, by omega⟩
  rw [show 2 * w / 2 = w by omega]
  push_cast
  ring

/-- **The leading coefficient, `+` direction**: the two classes of the
`(−⟨α,β⟩−1)`-st twisted product of two exponentials give `4^{−n}` in total. -/
theorem leading_plus (n ρ : ℤ) (I : ℕ) (hI : n.natAbs + n + 1 ≤ I) :
    ∑ i ∈ Finset.range I, cbinom (-(((0 : ℤ) : ℂ) / 2)) i * Vf n ρ (-n - 1 + i)
      + ∑ i ∈ Finset.range I, cbinom (-(((1 : ℤ) : ℂ) / 2)) i * Vf n (ρ - 1) (-n - 1 + i)
      = (1 / 2 : ℂ) ^ (n.natAbs + n).toNat * 2 ^ (n.natAbs - n).toNat := by
  rw [star_sum_Vf n ρ (-n - 1) _ I (by omega), star_sum_Vf n (ρ - 1) (-n - 1) _ I (by omega),
    ← Finset.sum_add_distrib]
  have hab : (n.natAbs + n).toNat + (n.natAbs - n).toNat = 2 * n.natAbs := by omega
  rw [← sum_gz_cbinom (n.natAbs + n).toNat (n.natAbs - n).toNat (2 * n.natAbs - 2 - ρ), hab]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [show (n.natAbs - (-n - 1) - 1).toNat = (n.natAbs + n).toNat by omega, ← mul_add]
  congr 1
  by_cases hpar : (u - ρ) % 2 = 0
  · rw [if_pos ⟨hpar, by omega⟩, if_neg (by omega), add_zero, cast_half_of_even (by omega)]
    congr 1
    push_cast
    ring
  · rw [if_neg (by tauto), if_pos ⟨by omega, by omega⟩, zero_add, cast_half_of_even (by omega)]
    congr 1
    push_cast
    ring

/-- **The leading coefficient, `−` direction** (for even `ρ`): `4ⁿ`. -/
theorem leading_minus (n ρ : ℤ) (hρ : ρ % 2 = 0) (I : ℕ) (hI : n.natAbs - n + 1 ≤ I) :
    ∑ i ∈ Finset.range I, cbinom (-(((0 : ℤ) : ℂ) / 2)) i * Vf n ρ (n - 1 + i)
      - ∑ i ∈ Finset.range I, cbinom (-(((1 : ℤ) : ℂ) / 2)) i * Vf n (ρ - 1) (n - 1 + i)
      = (1 / 2 : ℂ) ^ (n.natAbs - n).toNat * 2 ^ (n.natAbs + n).toNat := by
  rw [star_sum_Vf n ρ (n - 1) _ I (by omega), star_sum_Vf n (ρ - 1) (n - 1) _ I (by omega),
    ← Finset.sum_sub_distrib]
  have hab : (n.natAbs + n).toNat + (n.natAbs - n).toNat = 2 * n.natAbs := by omega
  rw [← sum_gz_cbinom_alt (n.natAbs + n).toNat (n.natAbs - n).toNat (2 * n.natAbs - 2 - ρ), hab]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [show (n.natAbs - (n - 1) - 1).toNat = (n.natAbs - n).toNat by omega, ← mul_sub]
  by_cases hpar : (u - ρ) % 2 = 0
  · rw [if_pos ⟨hpar, by omega⟩, if_neg (by omega), sub_zero, cast_half_of_even (by omega),
      Even.neg_one_pow (by rw [Nat.even_iff]; omega), one_mul]
    congr 1
    push_cast
    ring
  · rw [if_neg (by tauto), if_pos ⟨by omega, by omega⟩, zero_sub, cast_half_of_even (by omega),
      Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)]
    rw [neg_one_mul, mul_neg]
    congr 2
    push_cast
    ring

end VOA.Moonshine.LatticeTwisted
