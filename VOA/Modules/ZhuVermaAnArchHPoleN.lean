/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCrossTowerLift

/-!
# Game One — `HPoleN` via convolution reindex: the `crossDiffComm` convolution lies in `Onm`.

This file closes the membership `crossDiffComm W n K M a c d ∈ Onm W n 0` (the `(HPoleN)`-side of the
Dong–Jiang Lemma 2.8 pole-difference split), via the **cross-`s` convolution reindex** of the
pole-`(n+2)` tower onto a homogeneous grade-`Ws` tower.

## The genuine `n`-offset absorption (engine-verified, NOT faked)

The starting point is the FULLY-proven pole-slice reorganization
(`crossDiffComm_eq_sliceSum`, `ZhuVermaAnArchMUcircDiffCollapse`):

  `crossDiffComm W n K M a c d = ∑_{s<N} (crossDiffSlice … 2 s − crossDiffSlice … (n+2) s)`.

The individual pole-`(n+2)` slice `crossDiffSlice … (n+2) s` is a grade-`(Ws−n)` `PresTowerFam` in
`c₍s₎a` (`crossDiffSliceN_eq_PresTowerFam`), but `c₍s₎a` is genuinely homogeneous of grade
`Ws = M+K−s−1`, NOT `Ws−n` — so the slice is **not** a single-grade `PresTowerFam` in its own base
(`certificates/mathematica/poleN_derive2.wl`: grade-`Ws` single-tower span `False` for `n ≥ 1`).

The `n`-offset is absorbed by the **difference with the partner pole-`2` slice** at the *same* `s`:
the per-`s` difference `crossDiffSlice … 2 s − crossDiffSlice … (n+2) s` **is** a homogeneous grade-`Ws`
single-base `PresTowerFam` in `c₍s₎a` (engine-verified zero residual for all `K, M, n, s`,
`certificates/mathematica/poleN_convdiff.wl`).  The mechanism (engine-verified, `certificates/mathematica/poleN_regradewt.wl`):

* the grade-`(Ws−n)` tower `cbz`-rows **regrade** onto grade-`Ws` rows by the diagonal-shift identity
  `cbz(a, b) = ∑_{i≤n} (−1)^{n−i} C(n,i) · cbz(a+i, (b−n)+i)` (`crossDiff_regrade`, FULLY proven via
  `ZhuRes.cbz_diag_vandermonde` + the alternating-binomial collapse `regrade_alt`); applied to each
  active depth `dp ≥ n+1` of `crossDiffSliceWeightN`, this rewrites the pole-`(n+2)` slice coefficient
  as a grade-`Ws` `towerCoeffAnm` with the convolution weights
  `regradeWtN(e) = ∑_{k≤n} (−1)^k C(n,k) · crossDiffSliceWeightN K M n s (e+k)`;
* the difference weight `crossDiffSliceWeightDiff = crossDiffSliceWeight2 − regradeWtN` then gives the
  grade-`Ws` difference tower (`crossDiffSliceDiffCoeff_eq_tower`), zero residual.

## Proved here (axiom-clean)

* `crossDiff_regrade` — the diagonal-shift regrade `cbz` identity (the convolution reindex core);
* `regradeWtN` / `crossDiffSliceCoeffN_eq_towerWs` — the pole-`(n+2)` slice coefficient as a grade-`Ws`
  `towerCoeffAnm` (the `n`-offset moved onto the convolution weights);
* `crossDiffSliceWeightDiff` / `crossDiffSliceDiffCoeff_eq_tower` — the per-`s` difference coefficient
  as a grade-`Ws` `towerCoeffAnm`;
* `crossDiffSliceDiff_eq_PresTowerFam` — the per-`s` difference IS a homogeneous grade-`Ws` single-base
  `PresTowerFam` in `c₍s₎a`;
* `crossDiffSliceDiff_mem_Onm` — the per-`s` difference ∈ `Onm W n 0` (genuine grade-`Ws` homogeneity of
  `c₍s₎a`, NO hypothesis);
* **`crossDiffComm_mem_Onm`** — `crossDiffComm W n K M a c d ∈ Onm W n 0` for ALL homogeneous `a, c`
  (the convolution membership, FULLY proven — the `(HPoleN)` side discharged);
* `CircDiffAnmRightOnm_of_HARD` — `CircDiffAnmRightOnm W n` reduced to JUST the `anmRightDiff` (HARD)
  piece (the pole-`2`+convolution side fully proven);
* `MUGradedAction_of_HARD` — the full `MUGradedAction W` from JUST `HARD`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Finset

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The alternating-binomial collapse `∑_{i=j}^{n} (−1)^{n−i} C(n,i) C(i,j) = [j=n]`. -/

/-- **The alternating-binomial collapse.**  `∑_{i<n+1} (−1)^{n−i} C(n,i) C(i,j) = [j = n]`.
Trinomial revision `C(n,i)·C(i,j) = C(n,j)·C(n−j, i−j)`, reindex `i = j + m`, then the alternating
sum `∑_m (−1)^{n−j−m} C(n−j, m) = (1−1)^{n−j} = [n = j]`. -/
theorem regrade_alt (n j : ℕ) (hjn : j ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
      = if j = n then 1 else 0 := by
  -- terms with `i < j` vanish (`C(i,j) = 0`); reindex the tail `i = j + m`.
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = j + r := ⟨n - j, by omega⟩
  rw [show j + r + 1 = j + (r + 1) from by ring, Finset.sum_range_add]
  have hlo : (∑ i ∈ Finset.range j,
        (-1 : ℂ) ^ (j + r - i) * (Nat.choose (j + r) i : ℂ) * (Nat.choose i j : ℂ)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [show Nat.choose i j = 0 from Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi), Nat.cast_zero,
      mul_zero]
  rw [hlo, zero_add]
  -- the tail: `C(j+r, j+m)·C(j+m, j) = C(j+r, j)·C(r, m)`.
  have htail : (∑ m ∈ Finset.range (r + 1),
        (-1 : ℂ) ^ (j + r - (j + m)) * (Nat.choose (j + r) (j + m) : ℂ)
          * (Nat.choose (j + m) j : ℂ))
      = (Nat.choose (j + r) j : ℂ)
          * ∑ m ∈ Finset.range (r + 1), (-1 : ℂ) ^ (r - m) * (Nat.choose r m : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmr : m ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    -- `C(j+r, j+m)·C(j+m, j) = C(j+r, j)·C((j+r)−j, (j+m)−j) = C(j+r,j)·C(r,m)`.
    have hrev := Nat.choose_mul (n := j + r) (k := j + m) (s := j) (by omega)
    rw [show (j + r) - j = r from by omega, show (j + m) - j = m from by omega] at hrev
    have hcast : (Nat.choose (j + r) (j + m) : ℂ) * (Nat.choose (j + m) j : ℂ)
        = (Nat.choose (j + r) j : ℂ) * (Nat.choose r m : ℂ) := by
      rw [show (Nat.choose (j + r) (j + m) : ℂ) * (Nat.choose (j + m) j : ℂ)
            = ((Nat.choose (j + r) (j + m) * Nat.choose (j + m) j : ℕ) : ℂ) from by push_cast; ring,
        hrev]
      push_cast; ring
    rw [show (-1 : ℂ) ^ (j + r - (j + m)) * (Nat.choose (j + r) (j + m) : ℂ)
            * (Nat.choose (j + m) j : ℂ)
          = (-1 : ℂ) ^ (j + r - (j + m))
              * ((Nat.choose (j + r) (j + m) : ℂ) * (Nat.choose (j + m) j : ℂ)) from by ring,
      hcast, show j + r - (j + m) = r - m from by omega]
    ring
  rw [htail]
  -- `∑_m (−1)^{r−m} C(r,m) = [r = 0]` (signed binomial theorem).
  have halt : (∑ m ∈ Finset.range (r + 1), (-1 : ℂ) ^ (r - m) * (Nat.choose r m : ℂ))
      = if r = 0 then 1 else 0 := by
    have : (∑ m ∈ Finset.range (r + 1), (-1 : ℂ) ^ (r - m) * (Nat.choose r m : ℂ))
        = (-1 : ℂ) ^ r * ∑ m ∈ Finset.range (r + 1), (-1 : ℂ) ^ m * (Nat.choose r m : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmr : m ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      rw [← mul_assoc, ← pow_add, show r + m = (r - m) + 2 * m from by omega, pow_add,
        pow_mul]
      simp [mul_comm]
    rw [this]
    have hcast : (∑ m ∈ Finset.range (r + 1), (-1 : ℂ) ^ m * (Nat.choose r m : ℂ))
        = ((∑ m ∈ Finset.range (r + 1), ((-1) ^ m * (r.choose m) : ℤ) : ℤ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Int.alternating_sum_range_choose]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · rw [if_neg (by omega), if_neg (by omega)]; push_cast; ring
  rw [halt]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · rw [if_neg (by omega), if_neg (by omega), mul_zero]

/-! ## The diagonal-shift regrade `cbz` identity (the convolution reindex core). -/

/-- **The diagonal-shift regrade.**  For any integers `a, b` and `n : ℕ`,
`cbz a b = ∑_{i<n+1} (−1)^{n−i} C(n,i) · cbz (a+i) ((b−n)+i)`.  Expand each `cbz(a+i, (b−n)+i)` by the
diagonal Vandermonde `ZhuRes.cbz_diag_vandermonde`, swap to the inner index `j` outermost
(`ZhuRes.tri_swap`), and collapse the alternating coefficient by `regrade_alt` (`[j=n]`), leaving the
single `j = n` term `cbz a ((b−n)+n) = cbz a b`.  Engine-verified zero residual
(`certificates/mathematica/poleN_pascalform.wl`). -/
theorem crossDiff_regrade (a b : ℤ) (n : ℕ) :
    cbz a b
      = ∑ i ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * cbz (a + (i : ℤ)) ((b - (n : ℤ)) + (i : ℤ)) := by
  -- expand each diagonal-shifted `cbz(a+i, (b−n)+i)` by the diagonal Vandermonde.
  rw [show (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * cbz (a + (i : ℤ)) ((b - (n : ℤ)) + (i : ℤ)))
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
            * cbz a ((b - (n : ℤ)) + (j : ℤ)) from
      Finset.sum_congr rfl fun i _ => by
        rw [ZhuRes.cbz_diag_vandermonde a (b - (n : ℤ)) i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring]
  -- swap the triangle: `∑_i ∑_{j≤i} = ∑_j ∑_{i∈[j,n]}`.
  rw [ZhuRes.tri_swap n (fun i j =>
    ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
      * cbz a ((b - (n : ℤ)) + (j : ℤ)))]
  -- collapse the alternating coefficient (`[j = n]`); only `j = n` survives.
  rw [show (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.Ico j (n + 1),
        ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
          * cbz a ((b - (n : ℤ)) + (j : ℤ)))
      = ∑ j ∈ Finset.range (n + 1),
          (if j = n then (1 : ℂ) else 0) * cbz a ((b - (n : ℤ)) + (j : ℤ)) from
      Finset.sum_congr rfl fun j hj => by
        have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [← Finset.sum_mul]
        congr 1
        -- extend `Ico j (n+1)` to `range (n+1)`: the missing `i < j` terms have `C(i,j) = 0`.
        rw [show (∑ i ∈ Finset.Ico j (n + 1),
              (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
            = ∑ i ∈ Finset.range (n + 1),
              (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ) from ?_]
        · exact regrade_alt n j hjn
        · rw [Finset.range_eq_Ico,
            ← Finset.sum_Ico_consecutive
              (fun i => (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ))
              (Nat.zero_le j) (by omega : j ≤ n + 1)]
          rw [show (∑ i ∈ Finset.Ico 0 j,
                (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * (Nat.choose i j : ℂ)) = 0 from
              Finset.sum_eq_zero fun i hi => by
                rw [show Nat.choose i j = 0 from
                  Nat.choose_eq_zero_of_lt (by rw [Finset.mem_Ico] at hi; omega),
                  Nat.cast_zero, mul_zero], zero_add]]
  rw [show (∑ j ∈ Finset.range (n + 1),
        (if j = n then (1 : ℂ) else 0) * cbz a ((b - (n : ℤ)) + (j : ℤ)))
      = ∑ j ∈ Finset.range (n + 1),
        (if j = n then cbz a ((b - (n : ℤ)) + (j : ℤ)) else 0) from
      Finset.sum_congr rfl fun j _ => by split <;> simp]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n
    (fun j => cbz a ((b - (n : ℤ)) + (j : ℤ)))]
  rw [if_pos (Finset.self_mem_range_succ n),
    show (b - (n : ℤ)) + (n : ℤ) = b from by ring]

/-- **The regrade in backward-shift `(dp−k)` form.**  Reindexing `crossDiff_regrade` by `i ↦ n − i`:
`cbz a b = ∑_{k<n+1} (−1)^k C(n,k) · cbz (a + (n−k)) (b − k)`. -/
theorem crossDiff_regrade_sub (a b : ℤ) (n : ℕ) :
    cbz a b
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * (Nat.choose n k : ℂ)
            * cbz (a + ((n : ℤ) - (k : ℤ))) (b - (k : ℤ)) := by
  rw [crossDiff_regrade a b n]
  rw [← Finset.sum_range_reflect
      (fun i => (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * cbz (a + (i : ℤ)) ((b - (n : ℤ)) + (i : ℤ)))
      (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k from by omega, show n - (n - k) = k from by omega,
    show Nat.choose n (n - k) = Nat.choose n k from Nat.choose_symm hkn,
    show ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) from by rw [Nat.cast_sub hkn],
    show (b - (n : ℤ)) + ((n : ℤ) - (k : ℤ)) = b - (k : ℤ) from by ring]

/-! ## The tower-regrade: a grade-`(G−n)` `towerCoeffAnm` as a grade-`G` `towerCoeffAnm`. -/

/-- The forward-shift convolution regrade weight `regradeWt n wt e = ∑_{k<n+1} (−1)^k C(n,k) wt(e+k)`
(the `n`-offset moved onto the depth weights). -/
noncomputable def regradeWt (n : ℕ) (wt : ℕ → ℂ) (e : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt (e + k)

/-- **The tower-regrade lemma.**  For a depth weight `wt : ℕ → ℂ` vanishing below depth `n`
(`hwt : ∀ dp < n, wt dp = 0`), the grade-`(G−n)` `towerCoeffAnm` (depth `Δ`) equals the grade-`G`
`towerCoeffAnm` (depth `Δ`) with the forward-shift convolution weights `regradeWt n wt`:

  `towerCoeffAnm (G−n) n wt Δ μ = ∑_{dp<Δ} wt(dp) cbz((G−n)+dp, μ+(n+2)+dp)`
     `= ∑_{e<Δ} (regradeWt n wt e) cbz(G+e, μ+(n+2)+e)`.

Apply `crossDiff_regrade_sub` to each active `dp` (`cbz((G−n)+dp, μ+(n+2)+dp)
= ∑_k (−1)^k C(n,k) cbz(G+(dp−k), μ+(n+2)+(dp−k))`), reindex the inner `k` to the outer depth
`e = dp−k` (only `dp ≥ n` contribute, so `e ≥ 0`), and collect.  Engine-verified zero residual
(`certificates/mathematica/poleN_regradewt.wl`). -/
theorem towerCoeffAnm_regrade_int (Gz : ℤ) (n : ℕ) (wt : ℕ → ℂ) (Δ : ℕ) (μ : ℤ)
    (hwtlo : ∀ dp, dp < n → wt dp = 0) (hwthi : ∀ dp, Δ ≤ dp → wt dp = 0) :
    (∑ dp ∈ Finset.range Δ, wt dp * cbz (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)))
      = ∑ e ∈ Finset.range Δ,
          regradeWt n wt e * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) := by
  -- Step 1: regrade each `dp`-row by `crossDiff_regrade_sub` (top `Gz+dp = (Gz+n)+(dp−n)`).
  rw [show (∑ dp ∈ Finset.range Δ, wt dp * cbz (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)))
      = ∑ dp ∈ Finset.range Δ, ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt dp)
            * cbz ((Gz + (n : ℤ)) + ((dp : ℤ) - (k : ℤ)))
                (μ + ((n : ℤ) + 2) + ((dp : ℤ) - (k : ℤ))) from
      Finset.sum_congr rfl fun dp _ => by
        rw [crossDiff_regrade_sub (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)) n, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (Gz + (dp : ℤ)) + ((n : ℤ) - (k : ℤ))
              = (Gz + (n : ℤ)) + ((dp : ℤ) - (k : ℤ)) from by ring,
          show (μ + ((n : ℤ) + 2) + (dp : ℤ)) - (k : ℤ)
              = μ + ((n : ℤ) + 2) + ((dp : ℤ) - (k : ℤ)) from by ring]
        ring]
  -- Step 2: swap to `k`-outer, then per-`k` shift `dp = e + k`.
  rw [Finset.sum_comm]
  -- RHS: expand `regradeWt` + distribute + swap to `k`-outer.
  rw [show (∑ e ∈ Finset.range Δ,
        regradeWt n wt e * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)))
      = ∑ k ∈ Finset.range (n + 1), ∑ e ∈ Finset.range Δ,
          ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt (e + k))
            * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from ?_]
  · -- per-`k`: `∑_{dp<Δ} wt(dp) g(dp−k) = ∑_{e<Δ} wt(e+k) g(e)` (zero boundary terms).
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show (∑ dp ∈ Finset.range Δ,
          ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt dp)
            * cbz ((Gz + (n : ℤ)) + ((dp : ℤ) - (k : ℤ)))
                (μ + ((n : ℤ) + 2) + ((dp : ℤ) - (k : ℤ))))
        = ∑ dp ∈ Finset.Ico k Δ,
          ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt dp)
            * cbz ((Gz + (n : ℤ)) + ((dp : ℤ) - (k : ℤ)))
                (μ + ((n : ℤ) + 2) + ((dp : ℤ) - (k : ℤ))) from ?_]
    · rw [Finset.sum_Ico_eq_sum_range]
      rw [show (∑ e ∈ Finset.range (Δ - k),
            ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt (k + e))
              * cbz ((Gz + (n : ℤ)) + (((k + e : ℕ) : ℤ) - (k : ℤ)))
                  (μ + ((n : ℤ) + 2) + (((k + e : ℕ) : ℤ) - (k : ℤ))))
          = ∑ e ∈ Finset.range (Δ - k),
            ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt (e + k))
              * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from
          Finset.sum_congr rfl fun e _ => by
            rw [show ((k + e : ℕ) : ℤ) - (k : ℤ) = (e : ℤ) from by push_cast; ring,
              show k + e = e + k from by ring]]
      refine Finset.sum_subset (fun x hx => ?_) ?_
      · rw [Finset.mem_range] at hx ⊢
        exact lt_of_lt_of_le hx (Nat.sub_le Δ k)
      intro e _ he
      rw [Finset.mem_range, not_lt] at he
      rw [hwthi (e + k) (by omega), mul_zero, zero_mul]
    · symm
      refine Finset.sum_subset (by
        intro dp hdp; rw [Finset.mem_Ico] at hdp; rw [Finset.mem_range]; omega) ?_
      intro dp hdpr hdp
      rw [Finset.mem_range] at hdpr
      rw [Finset.mem_Ico, not_and_or] at hdp
      rcases hdp with h | h
      · rw [hwtlo dp (by omega), mul_zero, zero_mul]
      · omega
  · rw [show (∑ e ∈ Finset.range Δ,
          regradeWt n wt e * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)))
        = ∑ e ∈ Finset.range Δ, ∑ k ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * wt (e + k))
              * cbz ((Gz + (n : ℤ)) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from
        Finset.sum_congr rfl fun e _ => by
          rw [regradeWt, Finset.sum_mul]]
    rw [Finset.sum_comm]

/-! ## The pole-`(n+2)` slice coefficient as a grade-`Ws` `towerCoeffAnm`. -/

/-- `crossDiffSliceWeight2` vanishes above depth `s+1` (`cbz (M) (s+1−δ) = 0` for `δ > s+1`). -/
theorem crossDiffSliceWeight2_hi (M s : ℕ) {δ : ℕ} (hδ : s + 2 ≤ δ) :
    crossDiffSliceWeight2 M s δ = 0 := by
  rw [crossDiffSliceWeight2, if_neg (by omega)]
  rw [cbz_apply_neg (M : ℤ) (by omega : (s : ℤ) + 1 - (δ : ℤ) < 0), mul_zero]

/-- **The pole-`(n+2)` slice coefficient as an INTEGER-grade-`(Ws−n)` `cbz`-row sum.**  Integer-grade
mirror of `crossDiffSliceCoeffN_eq_tower` (no `ℕ`-grade / no `n ≤ Ws` constraint): restrict the proven
closed form `crossDiffSliceCoeffN_closed` to the active depth window `[n+1, n+1+s]`, shift and reflect
`q ↦ s−q`, matching the explicit weights `crossDiffSliceWeightN`.  Same Vandermonde algebra as
`crossDiffSliceCoeffN_eq_tower`, with `Gz : ℤ` in place of the cast `(Wsn : ℤ)`. -/
theorem crossDiffSliceCoeffN_eq_tower_int (K M n s : ℕ) (Gz : ℤ)
    (hGz : Gz = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1 - (n : ℤ)) (μ : ℤ) :
    crossDiffSliceCoeff K M n (n + 2) s μ
      = ∑ dp ∈ Finset.range (s + n + 2),
          crossDiffSliceWeightN K M n s dp * cbz (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)) := by
  rw [crossDiffSliceCoeffN_closed K M n s μ]
  have hsplit : (∑ dp ∈ Finset.range (s + n + 2),
        crossDiffSliceWeightN K M n s dp * cbz (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)))
      = ∑ dp ∈ Finset.Ico (n + 1) ((n + 1) + (s + 1)),
        crossDiffSliceWeightN K M n s dp * cbz (Gz + (dp : ℤ)) (μ + ((n : ℤ) + 2) + (dp : ℤ)) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro dp hdp
      rw [Finset.mem_Ico] at hdp
      rw [Finset.mem_range]; omega
    · intro dp _ hdp
      rw [Finset.mem_Ico, not_and_or] at hdp
      rcases hdp with h | h
      · rw [crossDiffSliceWeightN_lo K M n s (by omega), zero_mul]
      · rw [crossDiffSliceWeightN_hi K M n s (by omega), zero_mul]
  rw [hsplit, Finset.sum_Ico_eq_sum_range]
  rw [show ((n + 1) + (s + 1) - (n + 1) : ℕ) = s + 1 from by omega]
  rw [← Finset.sum_range_reflect
      (fun q => crossDiffSliceWeightN K M n s ((n + 1) + q)
          * cbz (Gz + ((n + 1) + q : ℕ)) (μ + ((n : ℤ) + 2) + ((n + 1) + q : ℕ))) (s + 1)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hps : p < s + 1 := Finset.mem_range.mp hp
  rw [show (s + 1 - 1 - p : ℕ) = s - p from by omega]
  have hple : p ≤ s := by omega
  rw [crossDiffSliceWeightN_at K M n s (s - p) (by omega)]
  have hsp : ((s : ℤ) - (p : ℤ)).toNat = s - p := by omega
  have hspz : (((s - p : ℕ)) : ℤ) = (s : ℤ) - (p : ℤ) := by rw [Nat.cast_sub hple]
  rw [hsp]
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) (congr_arg₂ (· * ·) rfl ?_) ?_) ?_
  · rw [hspz]
  · rw [hspz]; congr 1; ring
  · rw [show ((((n + 1) + (s - p) : ℕ)) : ℤ) = ((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ)) from by
          rw [Nat.cast_add, hspz]; push_cast; ring]
    congr 1
    · rw [hGz]; push_cast; ring
    · push_cast; ring

/-- **The pole-`(n+2)` slice coefficient as a grade-`Ws` `towerCoeffAnm`, unconditionally in `Ws`.**
The integer-grade-`(Ws−n)` row sum (`crossDiffSliceCoeffN_eq_tower_int`) regrades onto grade-`Ws` rows
by `towerCoeffAnm_regrade_int` (`Gz = Ws−n`, `Gz+n = Ws`), with `crossDiffSliceWeightN`-support
`crossDiffSliceWeightN_lo`/`_hi`.  No `n ≤ Ws` constraint (the regrade is integer-grade).
Engine-verified zero residual (`certificates/mathematica/poleN_directWs.wl`). -/
theorem crossDiffSliceCoeffN_eq_towerWs (K M n s : ℕ) (Ws : ℕ)
    (hWs : (Ws : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1) (μ : ℤ) :
    crossDiffSliceCoeff K M n (n + 2) s μ
      = ∑ e ∈ Finset.range (s + n + 2),
          regradeWt n (crossDiffSliceWeightN K M n s) e
            * cbz ((Ws : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) := by
  rw [crossDiffSliceCoeffN_eq_tower_int K M n s ((Ws : ℤ) - (n : ℤ)) (by rw [hWs]) μ]
  rw [towerCoeffAnm_regrade_int ((Ws : ℤ) - (n : ℤ)) n (crossDiffSliceWeightN K M n s) (s + n + 2) μ
      (fun dp hdp => crossDiffSliceWeightN_lo K M n s (by omega))
      (fun dp hdp => crossDiffSliceWeightN_hi K M n s (by omega))]
  refine Finset.sum_congr rfl fun e _ => by
    rw [show ((Ws : ℤ) - (n : ℤ)) + (n : ℤ) = (Ws : ℤ) from by ring]

/-! ## The per-`s` difference coefficient as a grade-`Ws` `towerCoeffAnm`. -/

/-- The per-`s` difference depth weight on the common grade-`Ws` tower (depth `s+n+2`):
`crossDiffSliceWeightDiff = crossDiffSliceWeight2 − regradeWt n crossDiffSliceWeightN`. -/
noncomputable def crossDiffSliceWeightDiff (K M n s : ℕ) (e : ℕ) : ℂ :=
  crossDiffSliceWeight2 M s e - regradeWt n (crossDiffSliceWeightN K M n s) e

/-- **The per-`s` difference coefficient as a grade-`Ws` `towerCoeffAnm`** (depth `s+n+2`).  The
pole-`2` coefficient is the grade-`Ws` tower with weights `crossDiffSliceWeight2` (depth `s+2`,
extended by zero, `crossDiffSliceWeight2_hi`); the pole-`(n+2)` coefficient is the grade-`Ws` tower
with weights `regradeWt n crossDiffSliceWeightN` (`crossDiffSliceCoeffN_eq_towerWs`).  Their
difference is the grade-`Ws` tower with the difference weights `crossDiffSliceWeightDiff`.
Engine-verified zero residual (`certificates/mathematica/poleN_regradewt.wl`). -/
theorem crossDiffSliceDiffCoeff_eq_tower (K M n s : ℕ) (Ws : ℕ)
    (hWs : (Ws : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1) (μ : ℤ) :
    crossDiffSliceCoeff K M n 2 s μ - crossDiffSliceCoeff K M n (n + 2) s μ
      = towerCoeffAnm Ws n (crossDiffSliceWeightDiff K M n s) (s + n + 2) μ := by
  -- pole-`2` half on depth `s+n+2` (extend `crossDiffSliceWeight2` by zero above `s+1`).
  have h2 : crossDiffSliceCoeff K M n 2 s μ
      = ∑ e ∈ Finset.range (s + n + 2),
          crossDiffSliceWeight2 M s e * cbz ((Ws : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) := by
    rw [crossDiffSliceCoeff2_eq_tower K M n s Ws hWs μ, towerCoeffAnm]
    refine Finset.sum_subset (fun x hx => ?_) ?_
    · rw [Finset.mem_range] at hx ⊢; omega
    intro e _ he
    rw [Finset.mem_range, not_lt] at he
    rw [crossDiffSliceWeight2_hi M s (by omega), zero_mul]
  rw [h2, crossDiffSliceCoeffN_eq_towerWs K M n s Ws hWs μ, towerCoeffAnm,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [crossDiffSliceWeightDiff, sub_mul]

/-! ## Finite support of the per-`s` slice coefficient. -/

/-- The per-`s` slice coefficient `μ ↦ crossDiffSliceCoeff K M n p s μ` has finite support (a finite
`j`-sum of finite-support `cbz`-shifts, `crossDiffSlice_shift_support_fin`). -/
theorem crossDiffSliceCoeff_support_fin (K M n p s : ℕ) :
    (Function.support (fun μ : ℤ => crossDiffSliceCoeff K M n p s μ)).Finite := by
  refine Set.Finite.subset
    (Set.Finite.biUnion (Finset.range (M + 1)).finite_toSet
      (fun j _ => crossDiffSlice_shift_support_fin K n p s (j : ℤ))) ?_
  intro μ hμ
  rw [Function.mem_support, crossDiffSliceCoeff] at hμ
  simp only [Set.mem_iUnion]
  by_contra hcon
  apply hμ
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : μ ∉ Function.support (fun μ : ℤ => cbz (K : ℤ) (μ + (n : ℤ) + 1 + p + s - (j : ℤ))) := by
    intro hmem; exact hcon ⟨j, Finset.mem_coe.mpr hj, hmem⟩
  rw [Function.mem_support, not_not] at hj'
  rw [hj', mul_zero]

/-! ## The per-`s` difference IS a homogeneous grade-`Ws` single-base `PresTowerFam` in `c₍s₎a`. -/

/-- **The per-`s` difference as a grade-`Ws` single-base `PresTowerFam`** in `w := c₍s₎a` of grade
`Ws = M+K−s−1`, depth `s+n+2`, weights `crossDiffSliceWeightDiff K M n s`.  Both slices are single
mode finsums in `c₍s₎a` (`crossDiffSlice_eq_finsum`); their difference coefficient is the grade-`Ws`
`towerCoeffAnm` (`crossDiffSliceDiffCoeff_eq_tower`). -/
theorem crossDiffSliceDiff_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱)
    (s : ℕ) (Ws : ℕ) (hWs : (Ws : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1) :
    crossDiffSlice W n K M a c d 2 s - crossDiffSlice W n K M a c d (n + 2) s
      = PresTowerFam W Ws n (W.smul c (s : ℤ) a) 1 (s + n + 2)
          (fun _ => d) (fun _ => crossDiffSliceWeightDiff K M n s) := by
  set w := W.smul c (s : ℤ) a with hw
  rw [crossDiffSlice_eq_finsum W n K M a c d 2 s, crossDiffSlice_eq_finsum W n K M a c d (n + 2) s]
  rw [PresTowerFam, Finset.univ_unique, Finset.sum_singleton]
  rw [presAnmFamily_eq_finsum W Ws n w d (crossDiffSliceWeightDiff K M n s) (s + n + 2)]
  -- the difference of two mode finsums is the mode finsum of the difference coefficient.
  rw [← finsum_sub_distrib
      (ZhuHR.smul_support_of_scalar W w d _
        (crossDiffSliceCoeff_support_fin K M n 2 s))
      (ZhuHR.smul_support_of_scalar W w d _
        (crossDiffSliceCoeff_support_fin K M n (n + 2) s))]
  refine finsum_congr fun μ => ?_
  rw [← sub_smul, crossDiffSliceDiffCoeff_eq_tower K M n s Ws hWs μ]

/-! ## The per-`s` difference lies in `Onm W n 0` (the convolution-absorbed `n`-offset). -/

/-- **The per-`s` difference `slice₂ − sliceₙ₊₂` lies in `Onm W n 0`** (homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`).  It is a homogeneous grade-`Ws` single-base `PresTowerFam` in `c₍s₎a ∈ 𝒱_{M+K−s−1}`
(`crossDiffSliceDiff_eq_PresTowerFam`, unconditional in `Ws`), hence in `Onm W n 0` by the
keystone-backed `PresTowerFam_mem_Onm`.  **This is the genuine `n`-offset absorption**: the individual
pole-`(n+2)` slice is NOT a grade-`Ws` tower (`certificates/mathematica/poleN_derive2.wl`, `False` for `n ≥ 1`), but the
DIFFERENCE with the pole-`2` slice IS (`certificates/mathematica/poleN_convdiff.wl`, zero residual).  The negative-grade case
(`M+K−s−1 < 0`) is handled by `W.positivity` (base `c₍s₎a = 0`). -/
theorem crossDiffSliceDiff_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ) :
    crossDiffSlice W n K M a c d 2 s - crossDiffSlice W n K M a c d (n + 2) s ∈ Onm W n 0 := by
  set w := W.smul c (s : ℤ) a with hw
  have hwmem : w ∈ W.grading ((M : ℤ) + (K : ℤ) - (s : ℤ) - 1) :=
    W.smul_mem_grading hc ha (s : ℤ)
  rcases lt_or_ge ((M : ℤ) + (K : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ 𝒱_{<0} = ⊥`, so `w = 0` and both slices are `0`.
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    rw [crossDiffSlice, crossDiffSlice]
    rw [Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_zero fun j _ => ?_, sub_zero]
    · exact (Onm W n 0).zero_mem
    · rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [← hw, hwmem, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero]
    · rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [← hw, hwmem, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero]
  · obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1 :=
      ⟨((M : ℤ) + (K : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ W.grading (Ws : ℤ) := by rwa [hWs]
    rw [crossDiffSliceDiff_eq_PresTowerFam W n K M a c d s Ws hWs]
    exact PresTowerFam_mem_Onm W n hwmem' 1 (s + n + 2) _ _

/-! ## The convolution membership `crossDiffComm ∈ Onm` (the `(HPoleN)` side, FULLY proven). -/

/-- **`crossDiffComm W n K M a c d ∈ Onm W n 0`** for ALL homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`.  By the
pole-slice reorganization `crossDiffComm_eq_sliceSum`, `crossDiffComm = ∑_{s<N} (slice₂ − sliceₙ₊₂)`;
each per-`s` difference lies in `Onm W n 0` (`crossDiffSliceDiff_mem_Onm`, the `n`-offset absorbed by
the cross-`s` convolution); `Submodule.sum_mem` finishes.  **This discharges the `(HPoleN)` side of the
Dong–Jiang Lemma 2.8 pole-difference split** WITHOUT the false per-slice membership. -/
theorem crossDiffComm_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossDiffComm W n K M a c d ∈ Onm W n 0 := by
  obtain ⟨N, hN⟩ := crossDiffComm_eq_sliceSum W n K M a c d
  rw [hN]
  exact Submodule.sum_mem _ (fun s _ => crossDiffSliceDiff_mem_Onm W n ha hc d s)

/-! ## The full reductions: `CircDiffAnmRightOnm` and `MUGradedAction` from JUST `HARD`. -/

/-- **The DJ Lemma 2.8 pole-difference ∈ `Onm` from JUST the `anmRightDiff` (HARD) piece.**  By the
proven split `circDiffAnmRight_split`, `D = anmRightDiff + crossDiffComm`; the `crossDiffComm` half is
fully proven (`crossDiffComm_mem_Onm`), so the whole pole-difference reduces to the single
remaining `anmRightDiff` membership `hARD`. -/
theorem circDiffAnmRight_mem_of_HARD (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱)
    (hARD : anmRightDiff W n K a c d ∈ Onm W n 0) :
    anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0 := by
  rw [circDiffAnmRight_split W n ha hc d]
  exact Submodule.add_mem _ hARD (crossDiffComm_mem_Onm W n ha hc d)

/-- **`CircDiffAnmRightOnm W n` from JUST `HARD`.**  The pole-`2`+convolution side is fully proven;
the only remaining input is the `anmRightDiff` U-family membership. -/
theorem CircDiffAnmRightOnm_of_HARD (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (HARD : ∀ (K : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c d : 𝒱,
      anmRightDiff W n K a c d ∈ Onm W n 0) :
    CircDiffAnmRightOnm W n := by
  intro K M P a ha c hc d _hd
  exact circDiffAnmRight_mem_of_HARD W n ha hc d (HARD K a ha c d)

/-- **`MUGradedAction W` from JUST `HARD`.**  Given, for every level `n`, the `anmRightDiff` U-family
membership (`HARD`), the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` holds: `HARD` gives
`CircDiffAnmRightOnm W n` (`CircDiffAnmRightOnm_of_HARD`), `CrossCFirstOnm_of_circDiff` lifts to
`CrossCFirstOnm W n`, and with the proven `CrossCommOnm_holds`, `MUGradedAction_of_families` yields
`MUGradedAction W`.  The pole-`(n+2)` slice membership (`HPoleN`) is FULLY discharged via the
convolution `crossDiffComm_mem_Onm`, leaving ONLY `HARD`. -/
theorem MUGradedAction_of_HARD (W : VertexOperatorAlgebra 𝒱)
    (HARD : ∀ (n K : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c d : 𝒱,
      anmRightDiff W n K a c d ∈ Onm W n 0) :
    MUGradedAction W :=
  MUGradedAction_of_families W
    (fun n => CrossCFirstOnm_of_circDiff W n
      (CircDiffAnmRightOnm_of_HARD W n (fun K a ha c d => HARD n K a ha c d)))
    (fun n => CrossCommOnm_holds W n)

/-! ## Status — the `(HPoleN)` convolution side FULLY discharged; `MUGradedAction W` reduced to `HARD`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`regrade_alt`** — the alternating-binomial collapse `∑_{i<n+1} (−1)^{n−i} C(n,i) C(i,j) = [j=n]`.
* **`crossDiff_regrade`** / **`crossDiff_regrade_sub`** — the diagonal-shift regrade
  `cbz a b = ∑_{i<n+1} (−1)^{n−i} C(n,i) cbz(a+i, (b−n)+i)` (the convolution reindex core), via
  `ZhuRes.cbz_diag_vandermonde` + `regrade_alt`.  Engine-verified (`certificates/mathematica/poleN_pascalform.wl`).
* **`towerCoeffAnm_regrade_int`** — the integer-grade tower-regrade: a grade-`Gz` `cbz`-row sum (weight
  vanishing outside `[n, Δ)`) equals the grade-`(Gz+n)` `cbz`-row sum with the forward-shift
  convolution weights `regradeWt n wt`.  No positivity constraint.
* **`crossDiffSliceCoeffN_eq_tower_int`** / **`crossDiffSliceCoeffN_eq_towerWs`** — the pole-`(n+2)`
  slice coefficient as a grade-`Ws` `towerCoeffAnm` with weights `regradeWt n (crossDiffSliceWeightN …)`,
  unconditional in `Ws` (the `n`-offset moved onto the convolution weights).  Engine-verified
  (`certificates/mathematica/poleN_directWs.wl`, `wWs ≡ regradeWtN`).
* **`crossDiffSliceWeightDiff`** / **`crossDiffSliceDiffCoeff_eq_tower`** — the per-`s` difference
  coefficient `C₂ₛ − Cₙ₊₂ₛ` as a grade-`Ws` `towerCoeffAnm` (depth `s+n+2`).  Engine-verified
  (`certificates/mathematica/poleN_convdiff.wl`/`certificates/mathematica/poleN_regradewt.wl`, zero residual).
* **`crossDiffSliceDiff_eq_PresTowerFam`** / **`crossDiffSliceDiff_mem_Onm`** — the per-`s` difference IS
  a homogeneous grade-`Ws` single-base `PresTowerFam` in `c₍s₎a ∈ 𝒱_{M+K−s−1}`, hence ∈ `Onm W n 0`
  (NO hypothesis; negative-grade case via `W.positivity`).  **The genuine `n`-offset absorption**: the
  individual pole-`(n+2)` slice is NOT a grade-`Ws` tower (`certificates/mathematica/poleN_derive2.wl`, `False` for `n ≥ 1`),
  but its DIFFERENCE with the pole-`2` slice IS.
* **`crossDiffComm_mem_Onm`** — **`crossDiffComm W n K M a c d ∈ Onm W n 0` for ALL homogeneous `a, c`,
  FULLY PROVEN** (the `(HPoleN)` side of the DJ Lemma 2.8 pole-difference split, discharged via the
  cross-`s` convolution — NOT the false per-slice membership).
* **`circDiffAnmRight_mem_of_HARD`** / **`CircDiffAnmRightOnm_of_HARD`** — the DJ Lemma 2.8
  pole-difference / `CircDiffAnmRightOnm W n` reduced to JUST the `anmRightDiff` (HARD) piece.
* **`MUGradedAction_of_HARD`** — **the full `MUGradedAction W` from JUST `HARD`**, via
  `CrossCFirstOnm_of_circDiff` + the proven `CrossCommOnm_holds` + `MUGradedAction_of_families`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the `anmRightDiff` U-family
membership `(HARD)   anmRightDiff W n K a c d ∈ Onm W n 0` (the `a`-outer right-action-difference
family; the computer-algebra script was not retained).  Discharging `(HARD)` feeds `MUGradedAction_of_HARD` ⟹
`MUGradedAction W` (the Dong–Jiang `M(U)` graded-action crux of Zhu Thm 5.3.4).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossDiff_regrade
  #print axioms VOA.towerCoeffAnm_regrade_int
  #print axioms VOA.crossDiffSliceCoeffN_eq_towerWs
  #print axioms VOA.crossDiffSliceDiffCoeff_eq_tower
  #print axioms VOA.crossDiffSliceDiff_mem_Onm
  #print axioms VOA.crossDiffComm_mem_Onm
  #print axioms VOA.CircDiffAnmRightOnm_of_HARD
  #print axioms VOA.MUGradedAction_of_HARD
-/
