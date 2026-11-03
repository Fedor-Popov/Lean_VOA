/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingResidue

/-!
# `ZhuVCore.v_core` — the associator's `v`-family scalar Vandermonde–Chu identity (Zhu Thm 2.1.2)

## Status
`sorry`-free, with no project axioms. **`v_core`** (with `alt_cbz`, `inn_alt`, `jSum`,
`jSum_trunc`, `inSum`, `split_a`) is an *unconditional* combinatorial identity, consumed by the
proved `VOA.associator_core` and hence by the unconditional `Ring (A 𝒱)`
(`ZhuRingInstance`). `#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Finset VOA
namespace ZhuVCore

open VOA.ZhuRes

/-- Alternating binomial sum `∑_{b<n+1} (-1)^b C(n,b) = [n=0]` over `cbz`, via Mathlib's
`Int.alternating_sum_range_choose` and the `cbz = nat-choose` bridge. -/
theorem alt_cbz (n : ℕ) :
    (∑ b ∈ Finset.range (n + 1), (-1 : ℂ) ^ b * cbz (n : ℤ) (b : ℤ))
      = if n = 0 then 1 else 0 := by
  have hcast : (∑ b ∈ Finset.range (n + 1), (-1 : ℂ) ^ b * cbz (n : ℤ) (b : ℤ))
      = ((∑ b ∈ Finset.range (n + 1), ((-1) ^ b * (n.choose b) : ℤ) : ℤ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hbn : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [cbz_natCast_eq_choose hbn]
  rw [hcast, Int.alternating_sum_range_choose]
  split <;> simp

/-- The shifted inner alternating sum:
`∑_{a<q+1} (-1)^a · C(q-s, a-s) = (-1)^s · [q = s]` for `s : ℕ`. -/
theorem inn_alt (q s : ℕ) :
    (∑ a ∈ Finset.range (q + 1), (-1 : ℂ) ^ a * cbz ((q : ℤ) - (s : ℤ)) ((a : ℤ) - (s : ℤ)))
      = (-1 : ℂ) ^ s * (if q = s then 1 else 0) := by
  rcases le_or_gt s q with hsq | hsq
  · -- `s ≤ q`: terms with `a < s` vanish; reindex the rest by `a = s + b`.
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = s + m := ⟨q - s, by omega⟩
    rw [show s + m + 1 = s + (m + 1) from by ring, Finset.sum_range_add]
    have hlo : (∑ a ∈ Finset.range s,
          (-1 : ℂ) ^ a * cbz ((↑(s + m) : ℤ) - (s : ℤ)) ((a : ℤ) - (s : ℤ))) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      rw [cbz_apply_neg _ (by have := Finset.mem_range.mp ha; omega), mul_zero]
    rw [hlo, zero_add]
    have hhi : (∑ b ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ (s + b) * cbz ((↑(s + m) : ℤ) - (s : ℤ)) ((↑(s + b) : ℤ) - (s : ℤ)))
        = (-1 : ℂ) ^ s * ∑ b ∈ Finset.range (m + 1), (-1 : ℂ) ^ b * cbz (m : ℤ) (b : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [show ((↑(s + m) : ℤ) - (s : ℤ)) = (m : ℤ) from by push_cast; ring,
        show ((↑(s + b) : ℤ) - (s : ℤ)) = (b : ℤ) from by push_cast; ring, pow_add]
      ring
    rw [hhi, alt_cbz m]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rw [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ s + m = s)]
  · -- `s > q`: every term has `a - s < 0`, so `cbz = 0`.
    rw [Finset.sum_eq_zero (fun a ha => by
      rw [cbz_apply_neg _ (by have := Finset.mem_range.mp ha; omega), mul_zero]),
      if_neg (by omega), mul_zero]

/-- The `J`-sum collapse:
`∑_{a<q+1} C(q,a)·(-1)^a·C(a-1,δ) = (-1)^δ · [q ≤ δ]`. -/
theorem jSum (q δ : ℕ) :
    (∑ a ∈ Finset.range (q + 1),
        cbz (q : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
      = (-1 : ℂ) ^ δ * (if q ≤ δ then 1 else 0) := by
  -- Step A: expand `C(a-1,δ)` by the alternating top-row Vandermonde, then swap to `t` outer.
  rw [show (∑ a ∈ Finset.range (q + 1),
            cbz (q : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
        = ∑ t ∈ Finset.range (δ + 1), ∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t
              * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ)))
              * (-1 : ℂ) ^ a from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => by
        rw [stepA (a : ℤ) δ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring]
  -- Step B: each `t`-term collapses (trinomial revision + `inn_alt`).
  have hterm : ∀ t ∈ Finset.range (δ + 1),
      (∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ))) * (-1 : ℂ) ^ a)
        = (-1 : ℂ) ^ t * cbz (q : ℤ) ((δ : ℤ) - (t : ℤ))
            * ((-1 : ℂ) ^ (δ - t) * (if q = δ - t then 1 else 0)) := by
    intro t ht
    have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [show (∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ))) * (-1 : ℂ) ^ a)
          = ∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * cbz (q : ℤ) ((δ : ℤ) - (t : ℤ))
              * ((-1 : ℂ) ^ a * cbz ((q : ℤ) - ((δ : ℤ) - (t : ℤ))) ((a : ℤ) - ((δ : ℤ) - (t : ℤ)))) from
        Finset.sum_congr rfl fun a _ => by rw [stepB q (a : ℤ) ((δ : ℤ) - (t : ℤ))]; ring]
    rw [← Finset.mul_sum]
    have hs : ((δ : ℤ) - (t : ℤ)) = ((δ - t : ℕ) : ℤ) := by rw [Nat.cast_sub htδ]
    rw [hs, inn_alt q (δ - t)]
  rw [Finset.sum_congr rfl hterm]
  -- Only the single index `t = δ - q` survives (when `q ≤ δ`).
  by_cases hqδ : q ≤ δ
  · rw [if_pos hqδ, mul_one]
    rw [Finset.sum_eq_single (δ - q)]
    · rw [if_pos (by omega : q = δ - (δ - q))]
      have h1 : ((δ : ℤ) - ((δ - q : ℕ) : ℤ)) = (q : ℤ) := by rw [Nat.cast_sub hqδ]; ring
      rw [h1, show cbz (q : ℤ) (q : ℤ) = 1 from by
        rw [cbz_natCast_eq_choose (le_refl q), Nat.choose_self]; norm_num]
      rw [mul_one, mul_one, ← pow_add]
      congr 1; omega
    · intro t ht htne
      have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      by_cases hqt : q = δ - t
      · exfalso; apply htne; omega
      · rw [if_neg hqt, mul_zero, mul_zero]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · rw [if_neg hqδ, mul_zero]
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [if_neg (by omega : ¬ q = δ - t), mul_zero, mul_zero]

/-- Truncation: a `jSum`-shaped sum over the larger range `K+1` equals `jSum m δ` when `m ≤ K`
(the extra terms vanish since `C(m, a) = 0` for `a > m`). -/
theorem jSum_trunc (K m δ : ℕ) (hmK : m ≤ K) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (m : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
      = (-1 : ℂ) ^ δ * (if m ≤ δ then 1 else 0) := by
  rw [← jSum m δ]
  refine (Finset.sum_subset
    (Finset.range_subset_range.mpr (by omega : m + 1 ≤ K + 1)) ?_).symm
  intro a _ hanotin
  have : m < a := by rw [Finset.mem_range] at hanotin; omega
  rw [cbz_lt (by positivity) (by exact_mod_cast this), zero_mul, zero_mul]

/-- The inner `a`-collapse `inSum`: for fixed `m : ℤ`,
`∑_{a<K+1} C(K,a)·C(K-a, m-a)·(-1)^δ·C(a-1,δ)·(-1)^a = [0 ≤ m ≤ δ] · C(K,m)`. -/
theorem inSum (K δ : ℕ) (m : ℤ) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
          * (-1 : ℂ) ^ δ * cbz ((a : ℤ) - 1) (δ : ℤ) * (-1 : ℂ) ^ a)
      = (if 0 ≤ m ∧ m ≤ (δ : ℤ) then cbz (K : ℤ) m else 0) := by
  -- Trinomial revision: `C(K,a)·C(K-a, m-a) = C(K,m)·C(m,a)`; factor out `C(K,m)·(-1)^δ`.
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
              * (-1 : ℂ) ^ δ * cbz ((a : ℤ) - 1) (δ : ℤ) * (-1 : ℂ) ^ a)
        = cbz (K : ℤ) m * (-1 : ℂ) ^ δ
            * ∑ a ∈ Finset.range (K + 1),
                cbz m (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
            = cbz (K : ℤ) m * cbz m (a : ℤ) from (stepB K m (a : ℤ)).symm]
      ring]
  rcases lt_or_ge m 0 with hm0 | hm0
  · rw [cbz_apply_neg (K : ℤ) hm0, if_neg (by omega), zero_mul, zero_mul]
  rcases le_or_gt m (K : ℤ) with hmK | hmK
  · -- `0 ≤ m ≤ K`: the inner sum truncates to `jSum m.toNat δ`.
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) := ⟨m.toNat, by omega⟩
    have hm'K : m' ≤ K := by exact_mod_cast hmK
    rw [jSum_trunc K m' δ hm'K]
    by_cases hm'δ : m' ≤ δ
    · rw [if_pos hm'δ, if_pos ⟨by positivity, by exact_mod_cast hm'δ⟩, mul_one]
      rw [show cbz (K : ℤ) (m' : ℤ) * (-1 : ℂ) ^ δ * (-1 : ℂ) ^ δ
            = cbz (K : ℤ) (m' : ℤ) * ((-1 : ℂ) ^ δ * (-1 : ℂ) ^ δ) from by ring,
        ← pow_add, show δ + δ = 2 * δ from by ring, pow_mul]
      norm_num
    · rw [if_neg hm'δ, if_neg (by omega : ¬ (0 ≤ (m' : ℤ) ∧ (m' : ℤ) ≤ (δ : ℤ))),
        mul_zero, mul_zero]
  · -- `m > K`: `C(K,m) = 0` kills both sides.
    have hz : cbz (K : ℤ) m = 0 := cbz_lt (by positivity) hmK
    rw [hz, zero_mul, zero_mul]
    split <;> simp

/-- Per-`a` dual-index split via the generalized-binomial Vandermonde:
`C(K+L-a, c) = ∑ᶠ i, C(L,i)·C(K-a, c-i)`. -/
theorem split_a (K L : ℕ) (c : ℤ) (a : ℕ) :
    cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) c
      = ∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K : ℤ) - (a : ℤ)) (c - i) := by
  rw [show (K : ℤ) + (L : ℤ) - (a : ℤ) = (L : ℤ) + ((K : ℤ) - (a : ℤ)) from by ring,
    ← cbz_vandermonde (L : ℤ) ((K : ℤ) - (a : ℤ)) c, cbzConvol]

/-- **The v-family scalar core of Zhu's associator** (Mathematica-verified over
`K,L,δ ≤ 6`, `γ ∈ [-6,8]`).  The generalized-binomial identity collapsing the `v`-family
double-residue into the right-hand convolution. -/
theorem v_core (K L : ℕ) (γ : ℤ) (δ : ℕ) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (K:ℤ) (a:ℤ)
          * cbz ((K:ℤ) + (L:ℤ) - (a:ℤ)) (γ + 2 + (δ:ℤ) - (a:ℤ))
          * ((-1:ℂ)^δ * gBinom ((a:ℤ) - 1) δ)
          * (-((-1:ℂ)^((a:ℤ) - 1))))
      = ∑ k ∈ Finset.range (δ + 1),
          cbz (L:ℤ) (γ + 2 + (k:ℤ)) * cbz (K:ℤ) ((δ:ℤ) - (k:ℤ)) := by
  -- Step 1: normalize each summand's sign factor and split the dual-index `cbz`.
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K:ℤ) (a:ℤ)
              * cbz ((K:ℤ) + (L:ℤ) - (a:ℤ)) (γ + 2 + (δ:ℤ) - (a:ℤ))
              * ((-1:ℂ)^δ * gBinom ((a:ℤ) - 1) δ)
              * (-((-1:ℂ)^((a:ℤ) - 1))))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℤ, cbz (L : ℤ) i
              * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                  * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a) from
      Finset.sum_congr rfl fun a _ => by
        -- sign algebra: `gBinom(a-1)δ = cbz(a-1)δ`, `-(-1)^(a-1) = (-1)^a`.
        have hgb : gBinom ((a:ℤ) - 1) δ = cbz ((a:ℤ) - 1) (δ:ℤ) := by
          rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
        have hsgn : (-((-1:ℂ)^((a:ℤ) - 1))) = (-1:ℂ)^a := by
          rw [zpow_sub₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_natCast]; simp [zpow_one]; ring
        rw [hgb, hsgn, split_a K L (γ + 2 + (δ:ℤ) - (a:ℤ)) a]
        rw [show (cbz (K:ℤ) (a:ℤ)
                  * (∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i))
                  * ((-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ)) * (-1:ℂ)^a)
              = (cbz (K:ℤ) (a:ℤ) * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a)
                  * (∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)) from by
          ring]
        rw [mul_finsum]
        refine finsum_congr fun i => ?_
        ring]
  -- Step 2: swap the finite `a`-sum with the `∑ᶠ i`, then collapse the inner `a`-sum via `inSum`.
  rw [sum_finsum_comm _ _ (fun a _ => ?_)]
  · -- the inner `a`-sum is `inSum K δ (γ+2+δ-i)`.
    rw [show (∑ᶠ i : ℤ, ∑ a ∈ Finset.range (K + 1),
              cbz (L : ℤ) i
                * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                    * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a))
          = ∑ᶠ i : ℤ, cbz (L : ℤ) i
              * (if 0 ≤ (γ + 2 + (δ:ℤ) - i) ∧ (γ + 2 + (δ:ℤ) - i) ≤ (δ : ℤ)
                  then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - i) else 0) from
        finsum_congr fun i => by
          rw [← Finset.mul_sum, ← inSum K δ (γ + 2 + (δ:ℤ) - i)]
          refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
          rw [show (γ + 2 + (δ:ℤ) - i) - (a:ℤ) = (γ + 2 + (δ:ℤ) - (a:ℤ)) - i from by ring]]
    -- Reindex `i = γ+2+k` (shift), then collapse the `[0,δ]`-supported finsum to the range sum.
    rw [← finsum_comp_equiv (Equiv.addLeft (γ + 2))
        (f := fun i : ℤ => cbz (L : ℤ) i
          * (if 0 ≤ (γ + 2 + (δ:ℤ) - i) ∧ (γ + 2 + (δ:ℤ) - i) ≤ (δ : ℤ)
              then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - i) else 0))]
    simp only [Equiv.coe_addLeft]
    rw [show (∑ᶠ k : ℤ, cbz (L : ℤ) (γ + 2 + k)
              * (if 0 ≤ (γ + 2 + (δ:ℤ) - (γ + 2 + k)) ∧ (γ + 2 + (δ:ℤ) - (γ + 2 + k)) ≤ (δ : ℤ)
                  then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - (γ + 2 + k)) else 0))
          = ∑ᶠ k : ℤ, cbz (L : ℤ) (γ + 2 + k)
              * (if 0 ≤ k ∧ k ≤ (δ : ℤ) then cbz (K : ℤ) ((δ:ℤ) - k) else 0) from
        finsum_congr fun k => by
          rw [show (γ + 2 + (δ:ℤ) - (γ + 2 + k)) = (δ:ℤ) - k from by ring]
          by_cases hk : 0 ≤ k ∧ k ≤ (δ : ℤ)
          · rw [if_pos ⟨by omega, by omega⟩, if_pos hk]
          · rw [if_neg (by omega), if_neg hk]]
    rw [finsumZ_eq_range_sum (N := δ + 1)
        (fun k : ℤ => cbz (L : ℤ) (γ + 2 + k)
          * (if 0 ≤ k ∧ k ≤ (δ : ℤ) then cbz (K : ℤ) ((δ:ℤ) - k) else 0))
        (fun p hp => by dsimp only; rw [if_neg (by omega), mul_zero])
        (fun p hp => by dsimp only; rw [if_neg (by omega), mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < δ + 1 := Finset.mem_range.mp hk
    rw [if_pos ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp this⟩]
  · -- finite support of each per-`a` finsum summand.
    apply Set.Finite.subset (cbz_convol_support_finite (L : ℤ) ((K:ℤ) - (a:ℤ))
      (γ + 2 + (δ:ℤ) - (a:ℤ)))
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro hzero
    apply hi
    have : cbz (L : ℤ) i
            * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a)
          = (cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i))
              * (cbz (K:ℤ) (a:ℤ) * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a) := by ring
    rw [this, hzero, zero_mul]

end ZhuVCore
