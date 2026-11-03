/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingResidue

/-!
# `ZhuMu.mu_identity` — the associator's `(1+x)`-basis change-of-basis core (Zhu Thm 2.1.2)

## Status
`sorry`-free, with no project axioms. **`mu_identity`** (with `muCoeff`, `delta_orth`,
`inner_lemma`, `cbz_symm`, `alt_row_sum`) is an *unconditional* combinatorial identity, consumed by
the proved `VOA.associator_core` and hence by the unconditional `Ring (A 𝒱)`
(`ZhuRingInstance`). `#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Finset VOA
open VOA.ZhuRes

namespace ZhuMu

/-! ## Helper: symmetry of `cbz` with a natural-number top index. -/

/-- Binomial symmetry for a natural top index: `C(N, j) = C(N, N - j)` (as `cbz`, all `j : ℤ`). -/
theorem cbz_symm (N : ℕ) (j : ℤ) :
    cbz (N : ℤ) j = cbz (N : ℤ) ((N : ℤ) - j) := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [cbz_apply_neg (N : ℤ) hj, cbz_lt (by positivity) (by omega : (N : ℤ) < (N : ℤ) - j)]
  rcases lt_or_ge (N : ℤ) j with hNj | hNj
  · rw [cbz_lt (by positivity) hNj,
      cbz_apply_neg (N : ℤ) (by omega : (N : ℤ) - j < 0)]
  -- `0 ≤ j ≤ N`: reduce both to `Nat.choose` and use `Nat.choose_symm`.
  obtain ⟨J, rfl⟩ : ∃ J : ℕ, j = (J : ℤ) := ⟨j.toNat, by omega⟩
  have hJN : J ≤ N := by exact_mod_cast hNj
  rw [show ((N : ℤ) - (J : ℤ)) = ((N - J : ℕ) : ℤ) from by rw [Nat.cast_sub hJN],
    cbz_natCast_eq_choose hJN, cbz_natCast_eq_choose (Nat.sub_le N J),
    Nat.choose_symm hJN]

/-! ## Helper: the alternating-row collapse `∑_{i≤m} (-1)^i C(m,i) = [m=0]`. -/

/-- `∑_{i ∈ range (m+1)} (-1)^i C(m,i) = cbz (m-1) m`, which is `1` if `m = 0` and `0` otherwise. -/
theorem alt_row_sum (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℂ) ^ i * cbz (m : ℤ) (i : ℤ)
      = cbz ((m : ℤ) - 1) (m : ℤ) := by
  have hv := vandermonde_range (-1 : ℤ) (m : ℤ) (m : ℤ) (N := m + 1) (by push_cast; omega)
  rw [show (-1 + (m : ℤ)) = (m : ℤ) - 1 from by ring] at hv
  rw [← hv]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [cbz_neg_one i]
  -- `cbz m (m - i) = cbz m i` by symmetry.
  rw [show ((m : ℤ) - (i : ℤ)) = (m : ℤ) - (i : ℤ) from rfl, ← cbz_symm m (i : ℤ)]

/-- `cbz (m-1) m = 0` when `m ≥ 1`. -/
theorem cbz_pred_top_succ {m : ℕ} (hm : 1 ≤ m) : cbz ((m : ℤ) - 1) (m : ℤ) = 0 :=
  cbz_lt (by omega) (by omega)

/-! ## The delta (orthogonality) identity. -/

/-- `∑_{n} (-1)^{kk-n} C(kk,n) C(n,i) = [kk = i]` (the Vandermonde orthogonality). Stated with the
range `n ∈ [0,kk]` and the sign written `(-1)^(kk-n)`. -/
theorem delta_orth (kk i : ℕ) :
    ∑ n ∈ Finset.range (kk + 1),
        (-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz (n : ℤ) (i : ℤ)
      = if kk = i then 1 else 0 := by
  -- trinomial revision: `cbz kk n * cbz n i = cbz kk i * cbz (kk-i) (n-i)`
  have hstep : ∀ n ∈ Finset.range (kk + 1),
      (-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz (n : ℤ) (i : ℤ)
        = cbz (kk : ℤ) (i : ℤ)
            * ((-1 : ℂ) ^ (kk - n) * cbz ((kk : ℤ) - (i : ℤ)) ((n : ℤ) - (i : ℤ))) := by
    intro n _
    have hb := stepB kk (n : ℤ) (i : ℤ)
    linear_combination ((-1 : ℂ) ^ (kk - n)) * hb
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  by_cases hki : i ≤ kk
  · -- reindex `n = i + u`, collapse the alternating row over `u ∈ [0, kk-i]`.
    have hsum : ∑ n ∈ Finset.range (kk + 1),
          ((-1 : ℂ) ^ (kk - n) * cbz ((kk : ℤ) - (i : ℤ)) ((n : ℤ) - (i : ℤ)))
        = (-1 : ℂ) ^ (kk - i) * cbz ((kk - i : ℕ) - 1 : ℤ) ((kk - i : ℕ) : ℤ) := by
      -- drop the `n < i` terms (the `cbz` factor vanishes there), shift `n = i + u`.
      rw [show ∑ n ∈ Finset.range (kk + 1),
              ((-1 : ℂ) ^ (kk - n) * cbz ((kk : ℤ) - (i : ℤ)) ((n : ℤ) - (i : ℤ)))
            = ∑ n ∈ Finset.Ico i (kk + 1),
              ((-1 : ℂ) ^ (kk - n) * cbz ((kk : ℤ) - (i : ℤ)) ((n : ℤ) - (i : ℤ))) from ?_]
      · rw [Finset.sum_Ico_eq_sum_range]
        rw [show kk + 1 - i = (kk - i) + 1 from by omega]
        have hcast2 : ((kk : ℤ) - (i : ℤ)) = ((kk - i : ℕ) : ℤ) := by rw [Nat.cast_sub hki]
        -- rewrite each term into `(-1)^(kk-i) * ((-1)^u * cbz (kk-i) u)`, factor and use `alt_row_sum`.
        rw [show ∑ u ∈ Finset.range ((kk - i) + 1),
                (-1 : ℂ) ^ (kk - (i + u)) * cbz ((kk : ℤ) - (i : ℤ)) (((i + u : ℕ) : ℤ) - (i : ℤ))
              = ∑ u ∈ Finset.range ((kk - i) + 1),
                (-1 : ℂ) ^ (kk - i) * ((-1 : ℂ) ^ u * cbz ((kk - i : ℕ) : ℤ) (u : ℤ)) from
            Finset.sum_congr rfl (fun u hu => ?_)]
        · rw [← Finset.mul_sum, alt_row_sum (kk - i)]
        · have hu' : u ≤ kk - i := by have := Finset.mem_range.mp hu; omega
          have hcast : (((i : ℕ) + u : ℕ) : ℤ) - (i : ℤ) = (u : ℤ) := by push_cast; ring
          rw [hcast, hcast2]
          have hsign : (-1 : ℂ) ^ (kk - (i + u)) = (-1 : ℂ) ^ (kk - i) * (-1 : ℂ) ^ u := by
            have he : (-1 : ℂ) ^ (kk - i) = (-1 : ℂ) ^ (kk - (i + u)) * (-1 : ℂ) ^ u := by
              rw [← pow_add, show kk - (i + u) + u = kk - i from by omega]
            rw [he, mul_assoc, ← pow_add, show u + u = 2 * u from by ring, pow_mul]
            simp
          rw [hsign]; ring
      · symm
        apply Finset.sum_subset
        · intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
        · intro x hx hxni
          simp only [Finset.mem_range] at hx
          simp only [Finset.mem_Ico, not_and, not_lt] at hxni
          have hxi : x < i := by by_contra h; have := hxni (by omega); omega
          rw [cbz_apply_neg ((kk : ℤ) - (i : ℤ)) (by omega : (x : ℤ) - (i : ℤ) < 0), mul_zero]
    rw [hsum]
    rcases eq_or_lt_of_le hki with heq | hlt
    · subst heq
      simp only [Nat.sub_self, Nat.cast_zero, pow_zero, one_mul, if_true]
      rw [show (0 : ℤ) - 1 = (-1 : ℤ) from by norm_num,
        show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, cbz_neg_one 0, pow_zero,
        cbz_natCast_eq_choose (le_refl i), Nat.choose_self]
      norm_num
    · -- `i < kk`, so `kk - i ≥ 1`, `cbz ((kk-i)-1)(kk-i) = 0`.
      rw [cbz_pred_top_succ (by omega : 1 ≤ kk - i), mul_zero, mul_zero, if_neg (by omega)]
  · -- `i > kk`: `cbz kk i = 0`, and `kk ≠ i`.
    rw [cbz_lt (by positivity) (by exact_mod_cast Nat.lt_of_not_le hki : (kk : ℤ) < (i : ℤ)),
      zero_mul, if_neg (by omega)]

/-- Integer-lower-index form of `delta_orth`: the inner `n`-sum picks out `j = kk`. -/
theorem delta_orth_int (kk : ℕ) (j : ℤ) :
    ∑ n ∈ Finset.range (kk + 1),
        (-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz (n : ℤ) j
      = if j = (kk : ℤ) then 1 else 0 := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rw [cbz_apply_neg (n : ℤ) hj, mul_zero]
  · obtain ⟨J, rfl⟩ : ∃ J : ℕ, j = (J : ℤ) := ⟨j.toNat, by omega⟩
    rw [delta_orth kk J]
    by_cases h : kk = J
    · rw [if_pos h, if_pos (by exact_mod_cast h.symm)]
    · rw [if_neg h, if_neg (by intro hc; exact h (by exact_mod_cast hc.symm))]

/-! ## The inner lemma. -/

theorem inner_lemma (K kk : ℕ) (s : ℤ) :
    ∑ n ∈ Finset.range (kk + 1),
        (-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz ((K : ℤ) + (n : ℤ)) (s + (n : ℤ))
      = cbz (K : ℤ) (s + (kk : ℤ)) := by
  rcases lt_or_ge ((K : ℤ) - s) 0 with hKs | hKs
  · -- `K - s < 0` (i.e. `s > K`): the lower index exceeds the top, so everything vanishes.
    have hrhs : cbz (K : ℤ) (s + (kk : ℤ)) = 0 :=
      cbz_lt (by positivity) (by omega)
    rw [hrhs]
    refine Finset.sum_eq_zero (fun n _ => ?_)
    rw [cbz_lt (show (0 : ℤ) ≤ (K : ℤ) + (n : ℤ) from by positivity)
        (show (K : ℤ) + (n : ℤ) < s + (n : ℤ) from by omega), mul_zero]
  -- `0 ≤ K - s`.  Set `N` large enough for the top-split Vandermonde to be exact.
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (K : ℤ) - s = (D : ℤ) := ⟨(K - s).toNat, by omega⟩
  set N : ℕ := D + 1 with hN
  -- Step 1: symmetry + top-split, then swap sums and apply the delta.
  rw [show ∑ n ∈ Finset.range (kk + 1),
          (-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz ((K : ℤ) + (n : ℤ)) (s + (n : ℤ))
        = ∑ n ∈ Finset.range (kk + 1), ∑ i ∈ Finset.range N,
            cbz (K : ℤ) (i : ℤ)
              * ((-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz (n : ℤ) (((D : ℤ)) - (i : ℤ))) from ?_]
  · -- swap, factor `cbz K i`, collapse inner via `delta_orth_int`.
    rw [Finset.sum_comm]
    rw [show ∑ i ∈ Finset.range N, ∑ n ∈ Finset.range (kk + 1),
            cbz (K : ℤ) (i : ℤ)
              * ((-1 : ℂ) ^ (kk - n) * cbz (kk : ℤ) (n : ℤ) * cbz (n : ℤ) (((D : ℤ)) - (i : ℤ)))
          = ∑ i ∈ Finset.range N,
            cbz (K : ℤ) (i : ℤ) * (if ((D : ℤ)) - (i : ℤ) = (kk : ℤ) then 1 else 0) from
        Finset.sum_congr rfl (fun i _ => by
          rw [← Finset.mul_sum, delta_orth_int kk ((D : ℤ) - (i : ℤ))])]
    -- the delta selects `i = D - kk` (when `kk ≤ D`); otherwise both sides vanish.
    by_cases hkD : kk ≤ D
    · rw [Finset.sum_eq_single (D - kk)]
      · rw [if_pos (by omega : ((D : ℤ)) - ((D - kk : ℕ) : ℤ) = (kk : ℤ))]
        rw [mul_one]
        -- `cbz K (D - kk) = cbz K (s + kk)`:  `D - kk = K - s - kk`, then symmetry.
        rw [show ((D - kk : ℕ) : ℤ) = (D : ℤ) - (kk : ℤ) from by push_cast [Nat.cast_sub hkD]; ring]
        rw [cbz_symm K (s + (kk : ℤ)), show (K : ℤ) - (s + (kk : ℤ)) = (D : ℤ) - (kk : ℤ) from by omega]
      · intro i _ hi
        rw [if_neg (by omega : ¬ ((D : ℤ)) - (i : ℤ) = (kk : ℤ)), mul_zero]
      · intro hni
        exact absurd (Finset.mem_range.mpr (by omega : D - kk < N)) hni
    · -- `kk > D`: no index satisfies `D - i = kk`, and `cbz K (s+kk) = 0`.
      rw [Finset.sum_eq_zero (fun i hi => by
        rw [if_neg (show ¬ ((D : ℤ)) - (i : ℤ) = (kk : ℤ) from by
          have := Finset.mem_range.mp hi; omega), mul_zero])]
      rw [cbz_lt (by positivity) (by omega : (K : ℤ) < s + (kk : ℤ))]
  · -- prove the term-wise rewrite (symmetry + Vandermonde top-split).
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show (K : ℤ) + (n : ℤ) = ((K + n : ℕ) : ℤ) from by push_cast; ring,
      cbz_symm (K + n) (s + (n : ℤ)),
      show ((K + n : ℕ) : ℤ) - (s + (n : ℤ)) = (D : ℤ) from by push_cast; omega]
    -- `cbz (K+n) D = ∑ i cbz K i * cbz n (D - i)` (Vandermonde top-split, `D < N`).
    have hv := vandermonde_range (K : ℤ) (n : ℤ) (D : ℤ) (N := N) (by push_cast [hN]; omega)
    rw [show ((K + n : ℕ) : ℤ) = (K : ℤ) + (n : ℤ) from by push_cast; ring, ← hv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)

/-! ## μ coefficients. -/

/-- μ(L,b,n) = the (1+x)-basis coefficients of Σ_{k≤b} C(L,b-k) x^k. -/
noncomputable def muCoeff (L b n : ℕ) : ℂ :=
  ∑ kk ∈ Finset.Icc n b, (-1:ℂ)^(kk-n) * cbz (L:ℤ) ((b:ℤ)-(kk:ℤ)) * cbz (kk:ℤ) (n:ℤ)

/-- `muCoeff` rewritten over the full range `[0,b]`: the extra terms (`kk < n`) carry `cbz kk n = 0`. -/
theorem muCoeff_range (L b n : ℕ) :
    muCoeff L b n
      = ∑ kk ∈ Finset.range (b + 1),
          (-1:ℂ)^(kk-n) * cbz (L:ℤ) ((b:ℤ)-(kk:ℤ)) * cbz (kk:ℤ) (n:ℤ) := by
  unfold muCoeff
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]; omega
  · intro x hx hxni
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_Icc, not_and, not_le] at hxni
    -- `x ∉ Icc n b` while `x ≤ b` forces `x < n`, so `cbz x n = 0`.
    rw [cbz_lt (show (0 : ℤ) ≤ (x : ℤ) from by positivity)
        (show (x : ℤ) < (n : ℤ) from by exact_mod_cast (by omega : x < n)), mul_zero]

theorem mu_identity (K L b : ℕ) (s : ℤ) :
    ∑ k ∈ Finset.range (b+1), cbz (K:ℤ) (s+(k:ℤ)) * cbz (L:ℤ) ((b:ℤ)-(k:ℤ))
      = ∑ n ∈ Finset.range (b+1), muCoeff L b n * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ)) := by
  -- Expand `muCoeff` over `[0,b]`, distribute, swap `n ↔ kk`.
  rw [show ∑ n ∈ Finset.range (b+1), muCoeff L b n * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ))
        = ∑ n ∈ Finset.range (b+1), ∑ kk ∈ Finset.range (b + 1),
            (-1:ℂ)^(kk-n) * cbz (L:ℤ) ((b:ℤ)-(kk:ℤ)) * cbz (kk:ℤ) (n:ℤ)
              * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ)) from
      Finset.sum_congr rfl (fun n _ => by
        rw [muCoeff_range L b n, Finset.sum_mul]),
    Finset.sum_comm]
  -- For each `kk`, factor out `cbz L (b-kk)` and collapse the inner `n`-sum by `inner_lemma`.
  refine Finset.sum_congr rfl (fun kk hkk => ?_)
  have hkkb : kk ≤ b := by have := Finset.mem_range.mp hkk; omega
  rw [show ∑ n ∈ Finset.range (b + 1),
            (-1:ℂ)^(kk-n) * cbz (L:ℤ) ((b:ℤ)-(kk:ℤ)) * cbz (kk:ℤ) (n:ℤ)
              * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ))
        = cbz (L:ℤ) ((b:ℤ)-(kk:ℤ))
            * ∑ n ∈ Finset.range (b + 1),
                (-1:ℂ)^(kk-n) * cbz (kk:ℤ) (n:ℤ) * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ)) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => by ring)]
  -- truncate inner sum to `range (kk+1)` (`cbz kk n = 0` for `n > kk`), then `inner_lemma`.
  rw [show ∑ n ∈ Finset.range (b + 1),
            (-1:ℂ)^(kk-n) * cbz (kk:ℤ) (n:ℤ) * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ))
        = ∑ n ∈ Finset.range (kk + 1),
            (-1:ℂ)^(kk-n) * cbz (kk:ℤ) (n:ℤ) * cbz ((K:ℤ)+(n:ℤ)) (s+(n:ℤ)) from ?_]
  · rw [inner_lemma K kk s]; ring
  · symm
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro x hx hxni
      simp only [Finset.mem_range, not_lt] at hx hxni
      rw [cbz_lt (show (0 : ℤ) ≤ (kk : ℤ) from by positivity)
        (show (kk : ℤ) < (x : ℤ) from by exact_mod_cast (by omega : kk < x)), mul_zero, zero_mul]

end ZhuMu
