/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossComm
import VOA.Modules.ZhuVermaAnArchMUcrossHM
import VOA.Modules.ZhuVermaAnArchMUcircClose
import VOA.Modules.ZhuVermaAnDescent2
import VOA.Modules.ZhuRingResidue

/-!
# Game One — closing **`CrossCommSliceTowerEq`** (the per-`s` shift-`0` commutator slice tower).

This file discharges the precise remaining identity of `ZhuVermaAnArchMUcrossComm`: the per-`s`
slice tower predicate `CrossCommSliceTowerEq W n K M a c d s Ws` (shift-`0`, mixed-level twin of the
proven `ZhuVermaAnDescent4.coeffSn_eq_coeffPn`).  Discharging it for all `s` closes `CrossCommOnm W n`
outright via `crossCommOnm_of_sliceTowerEq`, and — with the sibling `CrossCFirstOnm` — the full
`MUGradedAction W`.

## The per-`s` slice as a single mode finsum (the `coeffCommSlice` collapse)

The per-`s` slice (`ZhuVermaAnArchMUcrossComm`)

  `crossCommSlice W n K M a c d s
     = ∑_{j≤M} C(M,j) • ∑_{i≤K} C(K,i) • C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`,

has base `w := a₍s₎c` homogeneous of grade `Ws = K+M−s−1`.  Its mode `μ = (i+j)−(n+3+s)` runs as the
`j`-sum reindexes; collecting the `j`-sum into the mode finsum yields the single-`i`-sum
mode-coefficient

  `Cₛ(μ) = ∑_{i≤K} C(K,i) · C(i−n−1, s) · C(M, μ+n+3+s−i)`   (`crossCommSlice_eq_finsum`).

## The scalar core (the genuine `gen_jsum`-style combinatorial content)

The slice coefficient lies EXACTLY in the span of the `PresAnm`-coefficient functions
`μ ↦ C(Ws+δ, μ+(n+2)+δ)` (depths `δ = 1, …, s+1`), with the **explicit closed-form weights**

  `αδ = (−1)^{δ−1} · C(K, s+1−δ) · C(n+δ−1, δ−1)`   (engine-verified zero-residual, `M`-free).

This is `crossCommSlice_coeff_eq_tower`, proved off three standard binomial inputs (NOT a single
binomial — the genuine content): the generalized-binomial **Vandermonde**
`C(i−n−1, s) = ∑_p C(i, p)·C(−n−1, s−p)` (`vandermonde_range`), the **negative-top** row
`C(−n−1, s−p) = (−1)^{s−p}·C(n+s−p, s−p)` (`cbz_neg_succ`), and the **trinomial revision**
`C(K, i)·C(i, p) = C(K, p)·C(K−p, i−p)` (`stepB`), then the inner-`i` **Vandermonde**
`∑_i C(K−p, i−p)·C(M, μ+n+3+s−i) = C(K−p+M, μ+n+3+s−p)` (`vandermonde_range`), reindexed `δ = s−p`.
Engine value: `certificates/mathematica/cross_comm_slice{6,9,10,11}.wl` (zero `LeastSquares` residual for
every tested `(K, M, n, s, μ)`).

## What is proved here (axiom-clean)

* **`crossCommSlice_eq_finsum`** — the per-`s` slice as the single mode finsum `∑ᶠ μ, Cₛ(μ) • w₍μ₎d`.
* **`crossSliceWeight`** — the explicit closed-form depth weights `αδ` (padded `α₀ = 0`).
* **`crossCommSlice_coeff_eq_tower`** — **the scalar core**: `Cₛ(μ) = towerCoeffAnm Ws n
  (crossSliceWeight …) (s+2) μ` for every `μ` (the explicit `gen_jsum`-style identity).
* **`crossCommSlice_eq_PresTowerFam`** — the per-`s` slice IS a single-base `PresTowerFam` in `w`.
* **`CrossCommSliceTowerEq_holds`** — `CrossCommSliceTowerEq W n K M a c d s Ws` (∀ matching `Ws`),
  the precise remaining identity discharged.
* **`CrossCommOnm_holds`** — `CrossCommOnm W n`, via `crossCommOnm_of_sliceTowerEq`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-`s` slice mode-coefficient. -/

/-- The per-`s` slice mode-coefficient at mode `μ` (the single-`i`-sum, after collecting the `j`-sum
into the mode value `μ = (i+j)−(n+3+s)`):
`Cₛ(μ) = ∑_{i≤K} C(K,i) · C(i−n−1, s) · C(M, μ+n+3+s−i)`. -/
noncomputable def crossCommSliceCoeff (K M n s : ℕ) (μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
      * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))

/-- The explicit closed-form depth weights of the per-`s` slice tower (padded `α₀ = 0`):
`α₀ = 0`,  `αδ = (−1)^{δ−1} · C(n+δ−1, δ−1) · C(K, s+1−δ)`  for `δ = 1, …, s+1`.
Engine-verified (`certificates/mathematica/cross_comm_slice{5,6,11}.wl`); the explicit `gen_jsum`-style
coefficient table. -/
noncomputable def crossSliceWeight (K n s : ℕ) (δ : ℕ) : ℂ :=
  if δ = 0 then 0
  else (-1 : ℂ) ^ (δ - 1) * cbz ((n : ℤ) + (δ : ℤ) - 1) ((δ : ℤ) - 1)
        * cbz (K : ℤ) ((s : ℤ) + 1 - (δ : ℤ))

/-! ## Finite support of the per-`i` mode scalar (so the finite-sum / finsum swaps are valid). -/

/-- For fixed `i`, the scalar `μ ↦ cbz M (μ+n+3+s-i)` has finite support. -/
theorem crossSlice_shift_support_fin (M n s : ℕ) (i : ℤ) :
    (Function.support (fun μ : ℤ => cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - i))).Finite := by
  refine Set.Finite.subset (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity)
    ((n : ℤ) + 3 + s - i)) ?_
  intro μ hμ
  rw [Function.mem_support] at hμ ⊢
  intro h; apply hμ
  rwa [show μ + (n : ℤ) + 3 + s - i = μ + ((n : ℤ) + 3 + s - i) from by ring]

/-! ## The per-`s` slice as a single mode finsum. -/

/-- **The per-`s` slice in single-mode-finsum form.**  Collecting the `j`-sum (the mode source) into
the mode finsum, `crossCommSlice W n K M a c d s = ∑ᶠ μ, Cₛ(μ) • (a₍s₎c)₍μ₎ d`, with
`Cₛ = crossCommSliceCoeff K M n s` (the single-`i`-sum coefficient).  Shift-`0` twin of
`ZhuVermaAnDescent4.Sn_eq_finsum`. -/
theorem crossCommSlice_eq_finsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) (s : ℕ) :
    crossCommSlice W n K M a c d s
      = ∑ᶠ μ : ℤ, crossCommSliceCoeff K M n s μ
          • W.smul (W.smul a (s : ℤ) c) μ d := by
  set w := W.smul a (s : ℤ) c with hw
  rw [crossCommSlice]
  -- (a0) collapse each `(i,j)` term to a single combined-scalar smul, with the `i`-sum outermost.
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ) •
                  cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                    • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) * cbz (M : ℤ) (j : ℤ))
              • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul]
      congr 1; ring]
  -- (a) regroup as the coefficient-scaled inner `j`-sum.
  rw [show (∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) * cbz (M : ℤ) (j : ℤ))
              • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
  -- (b) per `i`, reindex the `j`-sum into a mode finsum (mode `μ = (i+j)-(n+3+s)`).
  rw [show (∑ i ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            ∑ᶠ μ : ℤ,
              ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d from
      Finset.sum_congr rfl fun i _ => by
        rw [show (∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ)
                    • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
              = ∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ)
                    • W.smul w ((j : ℤ) + ((i : ℤ) - (n : ℤ) - 3 - s)) d from
            Finset.sum_congr rfl fun j _ => by
              rw [show ((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)
                    = (j : ℤ) + ((i : ℤ) - (n : ℤ) - 3 - s) from by ring]]
        rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q)
            (fun q => W.smul w q d) ((i : ℤ) - (n : ℤ) - 3 - s)
            (fun q hq => cbz_apply_neg _ hq)
            (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
        -- pull the `i`-coefficient into the `q`-finsum.
        rw [smul_finsum' (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
            (f := fun q : ℤ => cbz (M : ℤ) q • W.smul w (q + ((i : ℤ) - (n : ℤ) - 3 - s)) d)
            (smul_support_of_scalar_gen (fun q : ℤ => cbz (M : ℤ) q)
              (fun q : ℤ => W.smul w (q + ((i : ℤ) - (n : ℤ) - 3 - s)) d)
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity) 0
                |>.subset (fun q hq => by
                  rw [Function.mem_support] at hq ⊢
                  intro h; apply hq; rwa [add_zero] at h)))]
        -- reindex `q ↦ μ = q + shift`.
        rw [← finsum_comp_equiv (Equiv.addRight ((i : ℤ) - (n : ℤ) - 3 - (s : ℤ)))
            (f := fun μ : ℤ =>
              ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d)]
        refine finsum_congr fun q => ?_
        simp only [Equiv.coe_addRight]
        rw [smul_smul,
          show (q + ((i : ℤ) - (n : ℤ) - 3 - (s : ℤ))) + (n : ℤ) + 3 + s - (i : ℤ) = q from by
            ring]]
  -- (c) swap `∑_i ∑ᶠ μ ↦ ∑ᶠ μ ∑_i` and assemble into `crossCommSliceCoeff`.
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun μ i => ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
          * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d)
      (fun i _ => ZhuHR.smul_support_of_scalar W w d _
        (Set.Finite.subset (crossSlice_shift_support_fin M n s (i : ℤ))
          (fun μ hμ => by
            rw [Function.mem_support] at hμ ⊢
            intro h; apply hμ
            rw [h, mul_zero])))]
  refine finsum_congr fun μ => ?_
  rw [crossCommSliceCoeff, Finset.sum_smul]

/-! ## The inner `i`-Vandermonde (with the `i−p` index shift). -/

/-- **The inner `i`-Vandermonde** (index shift `i ↦ i−p`): for `p ≤ K`,
`∑_{i≤K} C(K−p, i−p) · C(M, Y−i) = C(K−p+M, Y−p)`.  The `i = j+p` substitution turns the LHS into the
binomial convolution `∑ᶠ j, C(K−p, j)·C(M, (Y−p)−j) = C((K−p)+M, Y−p)` (`cbz_vandermonde`); the finite
range `[0,K]` covers the support (`C(K−p, i−p) = 0` for `i < p` and for `i > K`). -/
theorem crossSlice_inner_vandermonde (K M : ℕ) (p : ℕ) (hp : p ≤ K) (Y : ℤ) :
    (∑ i ∈ Finset.range (K + 1),
        cbz ((K : ℤ) - (p : ℤ)) ((i : ℤ) - (p : ℤ)) * cbz (M : ℤ) (Y - (i : ℤ)))
      = cbz ((K : ℤ) - (p : ℤ) + (M : ℤ)) (Y - (p : ℤ)) := by
  -- convert the finite range to a `∑ᶠ i : ℤ`, substitute `j = i - p`, recognize the convolution.
  rw [← ZhuRes.finsumZ_eq_range_sum
      (fun i : ℤ => cbz ((K : ℤ) - (p : ℤ)) (i - (p : ℤ)) * cbz (M : ℤ) (Y - i))
      (fun i hi => by
        dsimp only
        rw [cbz_apply_neg ((K : ℤ) - (p : ℤ)) (by omega), zero_mul])
      (fun i hi => by
        dsimp only
        rw [cbz_lt (by omega : (0 : ℤ) ≤ (K : ℤ) - (p : ℤ)) (by push_cast at hi ⊢; omega), zero_mul])]
  rw [← finsum_comp_equiv (Equiv.addRight (p : ℤ))
      (f := fun i : ℤ => cbz ((K : ℤ) - (p : ℤ)) (i - (p : ℤ)) * cbz (M : ℤ) (Y - i))]
  rw [← cbz_vandermonde ((K : ℤ) - (p : ℤ)) (M : ℤ) (Y - (p : ℤ)), cbzConvol]
  refine finsum_congr fun j => ?_
  simp only [Equiv.coe_addRight]
  rw [show (j + (p : ℤ)) - (p : ℤ) = j from by ring,
    show Y - (j + (p : ℤ)) = (Y - (p : ℤ)) - j from by ring]

/-! ## The scalar core — the per-`s` slice coefficient equals the `PresAnm`-tower coefficient. -/

/-- **The scalar core** (`gen_jsum`-style; engine-verified `M`-free, zero residual): the per-`s`
slice coefficient equals the `PresAnm`-tower coefficient with the explicit closed-form depth weights
`crossSliceWeight K n s` (depth `< s+2`, grade `Ws = K+M−s−1`):

  `Cₛ(μ) = ∑_{δ<s+2} (crossSliceWeight K n s δ) · C(Ws+δ, μ+(n+2)+δ)`  for every `μ`.

Proof: Vandermonde-split `C(i−n−1, s)` over `p`, negative-top `C(−n−1, s−p)`, trinomial revision
`C(K,i)·C(i,p)`, inner `i`-Vandermonde, then reindex `δ = s−p` (shift to `δ+1` for the tower). -/
theorem crossCommSlice_coeff_eq_tower (K M n s : ℕ) (Ws : ℕ)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) (μ : ℤ) :
    crossCommSliceCoeff K M n s μ
      = towerCoeffAnm Ws n (crossSliceWeight K n s) (s + 2) μ := by
  -- Step 1: Vandermonde-split `C(i-n-1,s) = ∑_p C(i,p) C(-n-1, s-p)`, then trinomial+neg-top per `i`,
  -- factoring the `p`-only scalar `A(p) = (-1)^(s-p) C(n+s-p,s-p) C(K,p)` out of the `i`-sum.
  rw [crossCommSliceCoeff]
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
              * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ)))
        = ∑ p ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
                * cbz (K : ℤ) (p : ℤ))
              * ∑ i ∈ Finset.range (K + 1),
                  cbz ((K : ℤ) - (p : ℤ)) ((i : ℤ) - (p : ℤ))
                    * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ)) from ?_]
  · -- Step 2: collapse each inner `i`-sum by the inner Vandermonde, reindex `δ = s - p`.
    rw [show (∑ p ∈ Finset.range (s + 1),
              ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                  * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
                  * cbz (K : ℤ) (p : ℤ))
                * ∑ i ∈ Finset.range (K + 1),
                    cbz ((K : ℤ) - (p : ℤ)) ((i : ℤ) - (p : ℤ))
                      * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ)))
          = ∑ p ∈ Finset.range (s + 1),
              ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                  * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
                  * cbz (K : ℤ) (p : ℤ))
                * cbz ((K : ℤ) - (p : ℤ) + (M : ℤ)) (μ + (n : ℤ) + 3 + s - (p : ℤ)) from
        Finset.sum_congr rfl fun p _ => by
          rcases le_or_gt p K with hpK | hpK
          · rw [crossSlice_inner_vandermonde K M p hpK (μ + (n : ℤ) + 3 + s)]
          · -- `p > K`: the outer scalar has factor `cbz K p = 0`, so both sides vanish.
            rw [cbz_lt (by positivity) (by exact_mod_cast hpK : (K : ℤ) < (p : ℤ))]
            ring]
    -- reindex `δ = s - p` (reflect `range (s+1)`), then identify with `towerCoeffAnm`.
    rw [towerCoeffAnm]
    -- `towerCoeffAnm` sums `δ ∈ range (s+2)`; the `δ = 0` term has weight `0`.
    rw [Finset.sum_range_succ' (fun δ =>
        crossSliceWeight K n s δ * cbz ((Ws : ℤ) + (δ : ℤ)) (μ + ((n : ℤ) + 2) + (δ : ℤ))) (s + 1)]
    rw [show crossSliceWeight K n s 0 = 0 from by rw [crossSliceWeight]; simp, zero_mul, add_zero]
    -- now both are `∑ over range (s+1)`; match termwise after the reflect `p = s - δ`.
    rw [← Finset.sum_range_reflect
        (fun p => ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
            * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
            * cbz (K : ℤ) (p : ℤ))
          * cbz ((K : ℤ) - (p : ℤ) + (M : ℤ)) (μ + (n : ℤ) + 3 + s - (p : ℤ))) (s + 1)]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    have hδs : δ < s + 1 := Finset.mem_range.mp hδ
    -- `p = s + 1 - 1 - δ = s - δ`; so `s - p = δ + 1`.
    have hpval : ((s + 1 - 1 - δ : ℕ) : ℤ) = (s : ℤ) - (δ : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hpval]
    -- LHS scalar: `(-1)^(s-(s-δ)) = (-1)^δ`; `s-(s-δ) = δ`.
    rw [show (s : ℤ) - ((s : ℤ) - (δ : ℤ)) = (δ : ℤ) from by ring]
    rw [show (δ : ℤ).toNat = δ from by omega]
    -- RHS weight at depth `δ+1`:
    rw [crossSliceWeight, if_neg (by omega)]
    rw [show δ + 1 - 1 = δ from by omega]
    -- match the `cbz` indices and scalars.
    rw [show ((δ + 1 : ℕ) : ℤ) - 1 = (δ : ℤ) from by push_cast; ring,
      show (n : ℤ) + ((δ + 1 : ℕ) : ℤ) - 1 = (n : ℤ) + (δ : ℤ) from by push_cast; ring,
      show (s : ℤ) + 1 - ((δ + 1 : ℕ) : ℤ) = (s : ℤ) - (δ : ℤ) from by push_cast; ring]
    -- the two `cbz` factors: top `K-(s-δ)+M = Ws + (δ+1)`, lower `μ+n+3+δ = μ+(n+2)+(δ+1)`.
    rw [show (K : ℤ) - ((s : ℤ) - (δ : ℤ)) + (M : ℤ) = (Ws : ℤ) + ((δ + 1 : ℕ) : ℤ) from by
        rw [hWs]; push_cast; ring,
      show μ + (n : ℤ) + 3 + s - ((s : ℤ) - (δ : ℤ)) = μ + ((n : ℤ) + 2) + ((δ + 1 : ℕ) : ℤ) from by
        push_cast; ring]
  · -- Step 1 detail: per `i`, Vandermonde-split + neg-top + trinomial, then swap `(i,p)` and factor.
    rw [show (∑ i ∈ Finset.range (K + 1),
              cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ)))
          = ∑ i ∈ Finset.range (K + 1), ∑ p ∈ Finset.range (s + 1),
              ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                  * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
                  * cbz (K : ℤ) (p : ℤ))
                * (cbz ((K : ℤ) - (p : ℤ)) ((i : ℤ) - (p : ℤ))
                    * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))) from
        Finset.sum_congr rfl fun i _ => by
          -- C(i-n-1,s) = ∑_p C(i,p) C(-n-1, s-p)  [vandermonde_range].
          have hv := ZhuRes.vandermonde_range (i : ℤ) (-((n : ℤ) + 1)) (s : ℤ)
            (N := s + 1) (by push_cast; omega)
          rw [show ((i : ℤ) + (-((n : ℤ) + 1))) = (i : ℤ) - ((n : ℤ) + 1) from by ring] at hv
          rw [← hv, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          -- neg-top: C(-n-1, s-p) = (-1)^(s-p) C(n+(s-p), s-p).
          have hneg : cbz (-((n : ℤ) + 1)) ((s : ℤ) - (p : ℤ))
              = (-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                  * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ)) := by
            rcases lt_or_ge ((s : ℤ) - (p : ℤ)) 0 with hsp | hsp
            · rw [cbz_apply_neg _ hsp, cbz_apply_neg _ hsp, mul_zero]
            · obtain ⟨q, hq⟩ : ∃ q : ℕ, (s : ℤ) - (p : ℤ) = (q : ℤ) :=
                ⟨((s : ℤ) - (p : ℤ)).toNat, by omega⟩
              rw [hq, Int.toNat_natCast]
              have hcq := ZhuRes.cbz_neg_succ n q
              rw [hcq]
          -- trinomial revision: C(K,i) C(i,p) = C(K,p) C(K-p, i-p)  [stepB].
          have hsb := ZhuRes.stepB K (i : ℤ) (p : ℤ)
          rw [hneg]
          rw [show cbz (K : ℤ) (i : ℤ)
                * (cbz (i : ℤ) (p : ℤ)
                    * ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                        * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))))
                * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))
              = ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                    * cbz ((n : ℤ) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ)))
                  * ((cbz (K : ℤ) (i : ℤ) * cbz (i : ℤ) (p : ℤ))
                      * cbz (M : ℤ) (μ + (n : ℤ) + 3 + s - (i : ℤ))) from by ring]
          rw [hsb]
          ring]
    -- swap `(i, p)` and factor the `p`-only scalar out of the `i`-sum.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]

/-! ## The per-`s` slice IS a single-base `PresTowerFam` in `a₍s₎c`. -/

/-- **The per-`s` slice as a single-base `PresTowerFam`.**  For grade `Ws = K+M−s−1`, the per-`s`
slice equals the single-base (`R = 1`, base `d`) `PresAnm`-tower family in `w := a₍s₎c` of depth
`s+2` with weights `crossSliceWeight K n s`:
`crossCommSlice W n K M a c d s = PresTowerFam W Ws n w 1 (s+2) (fun _ => d) (fun _ => crossSliceWeight K n s)`.
Proof: collapse the slice to its mode finsum (`crossCommSlice_eq_finsum`), the tower family to its
mode finsum (`presAnmFamily_eq_finsum`), and match per-mode by the scalar core
(`crossCommSlice_coeff_eq_tower`). -/
theorem crossCommSlice_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱)
    (s : ℕ) (Ws : ℕ) (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    crossCommSlice W n K M a c d s
      = PresTowerFam W Ws n (W.smul a (s : ℤ) c) 1 (s + 2)
          (fun _ => d) (fun _ => crossSliceWeight K n s) := by
  set w := W.smul a (s : ℤ) c with hw
  rw [crossCommSlice_eq_finsum W n K M a c d s]
  rw [PresTowerFam]
  -- single base `R = 1`: `∑ r : Fin 1, … = (the r=0 term)`.
  rw [Finset.univ_unique, Finset.sum_singleton]
  rw [presAnmFamily_eq_finsum W Ws n w d (crossSliceWeight K n s) (s + 2)]
  refine finsum_congr fun μ => ?_
  rw [crossCommSlice_coeff_eq_tower K M n s Ws hWs μ]

/-! ## `CrossCommSliceTowerEq` discharged. -/

/-- **`CrossCommSliceTowerEq W n K M a c d s Ws` discharged** (∀ matching `Ws`): the per-`s` slice
collapses onto a `PresAnm`-tower family in `a₍s₎c` (`crossCommSlice_eq_PresTowerFam`).  This is the
precise remaining identity of `ZhuVermaAnArchMUcrossComm`, engine-verified TRUE on the free boson
(`certificates/mathematica/cross_comm_slice{6,9,10,11}.wl`), fully proven. -/
theorem CrossCommSliceTowerEq_holds (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱)
    (s Ws : ℕ) (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    CrossCommSliceTowerEq W n K M a c d s Ws := by
  refine ⟨1, s + 2, fun _ => d, fun _ => crossSliceWeight K n s, ?_⟩
  exact crossCommSlice_eq_PresTowerFam W n K M a c d s Ws hWs

/-! ## `CrossCommOnm W n` discharged. -/

/-- **`CrossCommOnm W n`** (the cross commutator family membership), via the per-`s` tower predicate
discharged for all `s` (`CrossCommSliceTowerEq_holds`) and `crossCommOnm_of_sliceTowerEq`
(`ZhuVermaAnArchMUcrossComm`). -/
theorem CrossCommOnm_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : CrossCommOnm W n :=
  crossCommOnm_of_sliceTowerEq W n
    (fun _ _ _ a _ c _ d _ s Ws hWs => CrossCommSliceTowerEq_holds W n _ _ a c d s Ws hWs)

/-! ## Status — `CrossCommSliceTowerEq` and `CrossCommOnm` closed.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCommSlice_eq_finsum`** — the per-`s` slice as the single mode finsum `∑ᶠ μ, Cₛ(μ) • w₍μ₎d`.
* **`crossSlice_inner_vandermonde`** — the inner `i`-Vandermonde (index shift `i ↦ i−p`).
* **`crossCommSlice_coeff_eq_tower`** — **the scalar core**: `Cₛ(μ) = towerCoeffAnm Ws n
  (crossSliceWeight …) (s+2) μ`, the explicit `gen_jsum`-style identity (Vandermonde + neg-top +
  trinomial + inner Vandermonde, reindexed `δ = s−p`).
* **`crossCommSlice_eq_PresTowerFam`** — the per-`s` slice IS a single-base `PresTowerFam` in `a₍s₎c`.
* **`CrossCommSliceTowerEq_holds`** — the per-`s` tower predicate discharged (∀ matching `Ws`).
* **`CrossCommOnm_holds`** — `CrossCommOnm W n`, via `crossCommOnm_of_sliceTowerEq`.

The explicit closed-form depth weights `αδ = (−1)^{δ−1}·C(n+δ−1, δ−1)·C(K, s+1−δ)` (`crossSliceWeight`,
`δ = 1, …, s+1`; engine-verified `M`-free, zero `LeastSquares` residual) are the shift-`0`,
mixed-level twin of the `coeffSn_eq_coeffPn` collapse (`ZhuVermaAnDescent4`).  With the sibling
`CrossCFirstOnm`, this feeds the full `MUGradedAction W` (`MUGradedAction_of_families`,
`ZhuVermaAnArchMUcrossGen`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCommSlice_eq_finsum
  #print axioms VOA.crossSlice_inner_vandermonde
  #print axioms VOA.crossCommSlice_coeff_eq_tower
  #print axioms VOA.crossCommSlice_eq_PresTowerFam
  #print axioms VOA.CrossCommSliceTowerEq_holds
  #print axioms VOA.CrossCommOnm_holds
-/
