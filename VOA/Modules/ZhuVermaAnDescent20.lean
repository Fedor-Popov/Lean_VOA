/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent19
import VOA.Modules.ZhuVCore

/-!
# The depth-`n` **V-core** scalar collapse `VgammaModeColl = towerCoeff P n (wV ·) Δ μ`.

The MIRROR of the U-core (`ZhuVermaAnDescent19`): the second per-`(γ,μ)` scalar tower-collapse (the
`HV` input of `RightCircTowerEq_of_collapse`, `ZhuVermaAnDescent10`).  Over the frame
`VgammaModeColl_eq_directSum''` (`ZhuVermaAnDescent18`), the collected V-side scalar collapses onto
the grade-`P` `towerCoeff` tower with explicit weights `wV` and depth `Δ_V = (2n+2+max γ 0).toNat`
(vanishing for `γ < 0`, via the `if 0 ≤ γ` guard of `directVCoeff''`).

## V vs U divergence (verified)
The V-side third factor `cbz(γ+2n+1-i, γ)` carries NO `μ`, so the only `μ`-carrier is the *middle*
binomial `cbz(P+n+1+j, ·)`, forcing a grade-`P` tower (basis `cbz(P+n+δ, μ+2n+2+δ)`), and the
residual `M`-dependence of `VgammaModeColl` (the leading `cbz(M+n,·)` factor) lives inside the
weights `wV` (which are `P`- and `μ`-independent but `M`-dependent, unlike the `M`-independent `wU`).
The route re-bases the carrier `P+n+1+j → P+n` by a `(1+j)`-Vandermonde top-split before the
`tower_swap` (`ZhuVermaAnDescent19`), reusing `vandermonde_range_top`/`trinom_symm`/`tower_swap` and
the new signed Vandermonde `SV_collapse` (`∑_i (-1)^i cbz(Q,i) cbz(R-i, S) = cbz(R-Q, S-Q)`).

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/
open scoped BigOperators
open Finset
open VOA.ZhuRes
open ZhuUCore ZhuMu

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The new alternating Vandermonde `SV_collapse`. -/

/-- **Signed Vandermonde, support form.**  `∑_{i≤Q} (-1)^i C(Q,i) C(R-i, S) = C(R-Q, S-Q)`.
Proved by induction on `Q` via `cbz_pascal` (the recurrence `f(Q,R) = f(Q-1,R) - f(Q-1,R-1)`,
matching the Pascal recurrence of `C(R-Q, S-Q)`). -/
theorem SV_core (Q : ℕ) (R S : ℤ) :
    ∑ i ∈ Finset.range (Q + 1), (-1 : ℂ) ^ i * cbz (Q : ℤ) (i : ℤ) * cbz (R - (i : ℤ)) S
      = cbz (R - (Q : ℤ)) (S - (Q : ℤ)) := by
  induction Q generalizing R with
  | zero => simp
  | succ q ih =>
    have hcast : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    -- Split via Pascal `C(q+1,i) = C(q,i) + C(q,i-1)`.
    rw [show ∑ i ∈ Finset.range (q + 1 + 1),
            (-1 : ℂ) ^ i * cbz ((q : ℤ) + 1) (i : ℤ) * cbz (R - (i : ℤ)) S
          = (∑ i ∈ Finset.range (q + 1 + 1),
              (-1 : ℂ) ^ i * cbz (q : ℤ) (i : ℤ) * cbz (R - (i : ℤ)) S)
            + (∑ i ∈ Finset.range (q + 1 + 1),
              (-1 : ℂ) ^ i * cbz (q : ℤ) ((i : ℤ) - 1) * cbz (R - (i : ℤ)) S) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hpas : cbz ((q : ℤ) + 1) (i : ℤ) = cbz (q : ℤ) (i : ℤ) + cbz (q : ℤ) ((i : ℤ) - 1) := by
        have := cbz_pascal ((q : ℤ) + 1) (i : ℤ)
        rw [show (q : ℤ) + 1 - 1 = (q : ℤ) from by ring] at this
        exact this
      rw [hpas]; ring]
    -- First sum: truncate to `range (q+1)` (the `i=q+1` term has `C(q,q+1)=0`), then `ih R`.
    rw [show (∑ i ∈ Finset.range (q + 1 + 1),
            (-1 : ℂ) ^ i * cbz (q : ℤ) (i : ℤ) * cbz (R - (i : ℤ)) S)
          = ∑ i ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ i * cbz (q : ℤ) (i : ℤ) * cbz (R - (i : ℤ)) S from by
      rw [Finset.sum_range_succ]
      rw [show cbz (q : ℤ) ((q + 1 : ℕ) : ℤ) = 0 from by
            rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : q < q + 1))],
        mul_zero, zero_mul, add_zero]]
    rw [ih R]
    -- Second sum: reindex `i ↦ i+1` (the `i=0` term has `C(q,-1)=0`), giving `-(ih (R-1))`.
    rw [show (∑ i ∈ Finset.range (q + 1 + 1),
            (-1 : ℂ) ^ i * cbz (q : ℤ) ((i : ℤ) - 1) * cbz (R - (i : ℤ)) S)
          = - ∑ i ∈ Finset.range (q + 1),
              (-1 : ℂ) ^ i * cbz (q : ℤ) (i : ℤ) * cbz ((R - 1) - (i : ℤ)) S from by
      rw [Finset.sum_range_succ']
      -- bottom term `i=0`: `C(q,-1)=0`.
      rw [show (-1 : ℂ) ^ 0 * cbz (q : ℤ) ((0 : ℕ) - 1 : ℤ) * cbz (R - (0 : ℕ)) S = 0 from by
            rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by norm_num,
              cbz_apply_neg (q : ℤ) (by norm_num), mul_zero, zero_mul], add_zero]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) from by push_cast; ring,
        show R - ((i + 1 : ℕ) : ℤ) = (R - 1) - (i : ℤ) from by push_cast; ring,
        pow_succ]
      ring]
    rw [ih (R - 1)]
    -- `C(R-q, S-q) - C((R-1)-q, S-q) = C(R-(q+1), S-(q+1))` (Pascal in the top, `cbz_pascal`).
    have hp := cbz_pascal (R - (q : ℤ)) (S - (q : ℤ))
    rw [show R - (q : ℤ) - 1 = (R - 1) - (q : ℤ) from by ring] at hp
    rw [show R - ((q : ℤ) + 1) = (R - 1) - (q : ℤ) from by ring,
      show S - ((q : ℤ) + 1) = (S - (q : ℤ)) - 1 from by ring]
    -- `hp : C(R-q, S-q) = C((R-1)-q, S-q) + C((R-1)-q, (S-q)-1)`.
    linear_combination hp

/-- **Signed Vandermonde, range form** (the `SR_collapse` analogue used by the V-core): the support
`[0,Q]` of the first factor lies in `[0,N)`. -/
theorem SV_collapse (Q : ℕ) (R S : ℤ) {N : ℕ} (hQ : Q < N) :
    ∑ i ∈ Finset.range N, (-1 : ℂ) ^ i * cbz (Q : ℤ) (i : ℤ) * cbz (R - (i : ℤ)) S
      = cbz (R - (Q : ℤ)) (S - (Q : ℤ)) := by
  rw [← SV_core Q R S]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega : Q + 1 ≤ N)) ?_).symm
  intro i _ hi
  have : Q < i := by rw [Finset.mem_range] at hi; omega
  rw [cbz_lt (by positivity) (by exact_mod_cast this), mul_zero, zero_mul]

/-! ## The `(-1)^(i-2n-2) = (-1)^i` sign normalization. -/

/-- The V-core sign `(-1)^((i:ℤ)-2n-2)` (a `zpow`) equals the `Nat`-power `(-1)^i`
(since `2n+2` is even). -/
theorem vsign_eq (n i : ℕ) :
    (-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2) = (-1 : ℂ) ^ i := by
  rw [show (i : ℤ) - 2 * (n : ℤ) - 2 = (i : ℤ) + (-(2 * (n : ℤ) + 2)) from by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast,
    show -(2 * (n : ℤ) + 2) = -((2 * n + 2 : ℕ) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast]
  rw [show (-1 : ℂ) ^ (2 * n + 2) = 1 from by
    rw [show 2 * n + 2 = 2 * (n + 1) from by ring, pow_mul]; norm_num]
  simp

/-! ## The per-`j` inner `i`-sum `VInnerI` and the structural reduction `VgammaModeColl_eq_jSum`. -/

/-- The V-side inner `i`-sum at fixed FZ index `j`: the middle binomial's top written as `A-i`
(`A = M+P+2n+1+j`), the always-true guard dropped, and the sign normalized to `(-1)^i`. -/
noncomputable def VInnerI (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1),
    cbz ((M : ℤ) + n) (i : ℤ)
      * cbz (((M : ℤ) + P + 2 * n + 1 + j) - i) ((M : ℤ) + P - n - 2 - μ - γ)
      * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)

/-- **Structural reduction of `VgammaModeColl` to the `j`-sum of `VInnerI`.**  For `γ < 0` both
sides vanish (the `directVCoeff''` guard `if 0 ≤ γ`).  For `γ ≥ 0`, the always-true `ucore_guard`
drops the inner `if`, `(G i)+j = A-i`, and `vsign_eq` normalizes the sign. -/
theorem VgammaModeColl_eq_jSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeColl M P n G γ μ
      = if 0 ≤ γ then
          ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * VInnerI M P n j γ μ
        else 0 := by
  rw [VgammaModeColl_eq_directSum'' M P n G hG γ μ]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [VInnerI, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
    have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := ucore_guard M P n i hile
    rw [directVCoeff'', if_pos hγ, if_pos hgr, hG i hgr, vsign_eq n i]
    have htop : ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) + (j : ℤ)
        = ((M : ℤ) + P + 2 * n + 1 + j) - i := by ring
    rw [htop]
    ring
  · rw [if_neg hγ]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [directVCoeff'', if_neg hγ]

/-! ## The per-`a` V-inner collapse `VIC_collapse` and the `a`-sum `VASum`. -/

/-- **The per-`a` inner `i`-collapse** (V mirror of `IC_collapse`).  For `a ≤ M+n`,
`∑_i C(M+n,i)·C(M+n-i,a)·((-1)^i C(γ+2n+1-i, γ)) = C(M+n,a)·C(γ+n+1-M+a, γ-M-n+a)`.  Via
`trinom_symm` (pull `C(M+n,a)` out) and `SV_collapse` (`Q = M+n-a`, `R = γ+2n+1`, `S = γ`). -/
theorem VIC_collapse (M n a : ℕ) (γ : ℤ) (ha : a ≤ M + n) :
    ∑ i ∈ Finset.range (M + n + 1),
        cbz ((M : ℤ) + n) (i : ℤ) * cbz ((M : ℤ) + n - (i : ℤ)) (a : ℤ)
          * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ)
      = cbz ((M : ℤ) + n) (a : ℤ) * cbz (γ + (n : ℤ) + 1 - M + a) (γ - M - n + a) := by
  rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring]
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M + n : ℕ) : ℤ) (i : ℤ) * cbz (((M + n : ℕ) : ℤ) - (i : ℤ)) (a : ℤ)
              * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ)
        = cbz ((M + n : ℕ) : ℤ) (a : ℤ)
            * ∑ i ∈ Finset.range (M + n + 1),
                (-1 : ℂ) ^ i * cbz (((M + n : ℕ) : ℤ) - (a : ℤ)) (i : ℤ)
                  * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [trinom_symm (M + n) (i : ℤ) (a : ℤ)]; ring]
  -- the remaining `i`-sum is `SV_collapse` with `Q = M+n-a`, `R = γ+2n+1`, `S = γ`.
  have hcast : ((M + n - a : ℕ) : ℤ) = (M : ℤ) + n - a := by rw [Nat.cast_sub ha]; push_cast; ring
  rw [show (∑ i ∈ Finset.range (M + n + 1),
            (-1 : ℂ) ^ i * cbz (((M + n : ℕ) : ℤ) - (a : ℤ)) (i : ℤ)
              * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ)
        = ∑ i ∈ Finset.range (M + n + 1),
            (-1 : ℂ) ^ i * cbz ((M + n - a : ℕ) : ℤ) (i : ℤ)
              * cbz ((γ + 2 * (n : ℤ) + 1) - (i : ℤ)) γ from
      Finset.sum_congr rfl fun i _ => by
        rw [show ((M + n : ℕ) : ℤ) - (a : ℤ) = ((M + n - a : ℕ) : ℤ) from by rw [hcast]; push_cast; ring,
          show γ + 2 * (n : ℤ) + 1 - (i : ℤ) = (γ + 2 * (n : ℤ) + 1) - (i : ℤ) from by ring]]
  rw [SV_collapse (M + n - a) (γ + 2 * (n : ℤ) + 1) γ (N := M + n + 1) (by omega), hcast]
  rw [show ((M + n : ℕ) : ℤ) = (M : ℤ) + n from by push_cast; ring,
    show (γ + 2 * (n : ℤ) + 1) - ((M : ℤ) + n - a) = γ + (n : ℤ) + 1 - M + a from by ring,
    show γ - ((M : ℤ) + n - a) = γ - M - n + a from by ring]

/-- The V `a`-sum (R3-V's RHS). -/
noncomputable def VASum (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range (M + n + 1),
    cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
      * cbz ((M : ℤ) + n) (a : ℤ)
      * cbz (γ + (n : ℤ) + 1 - M + a) (γ - M - n + a)

/-- **R3-V** (the V mirror of `InnerI_eq_ASum`).  Expand the middle binomial `C(A-i, K0)` by the
Vandermonde top-split (`vandermonde_range_top`), swap to `a`-outer, factor the `i`-independent
`C(P+n+1+j, K0-a)`, and collapse each inner `i`-sum by `VIC_collapse`. -/
theorem VInnerI_eq_VASum (M P n j : ℕ) (γ μ : ℤ) :
    VInnerI M P n j γ μ = VASum M P n j γ μ := by
  rw [VInnerI, VASum]
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ)
              * cbz (((M : ℤ) + P + 2 * n + 1 + j) - i) ((M : ℤ) + P - n - 2 - μ - γ)
              * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)
        = ∑ i ∈ Finset.range (M + n + 1), ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
              * (cbz ((M : ℤ) + n) (i : ℤ) * cbz (((M : ℤ) + n) - (i : ℤ)) (a : ℤ)
                  * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)) from
      Finset.sum_congr rfl fun i hi => ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [← Finset.mul_sum, VIC_collapse M n a γ hale]
    ring
  · have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
    have hmid : cbz (((M : ℤ) + P + 2 * n + 1 + j) - i) ((M : ℤ) + P - n - 2 - μ - γ)
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((M + n - i : ℕ) : ℤ) (a : ℤ)
              * cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a) := by
      rw [vandermonde_range_top (M + n - i) ((P : ℤ) + n + 1 + j)
        ((M : ℤ) + P - n - 2 - μ - γ) (N := M + n + 1) (by omega)]
      congr 1
      rw [Nat.cast_sub hile]; push_cast; ring
    rw [hmid, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((M + n - i : ℕ) : ℤ) = (M : ℤ) + n - i from by rw [Nat.cast_sub hile]; push_cast; ring]
    ring

/-! ## The `k`-form of `VASum` (reflect `a ↦ (M+n)-a`, flip the middle by symmetry, shift `b = (γ+n+1+j)-k`). -/

/-- The (M-DEPENDENT, P-independent) per-`(j,k)` V kernel `VHkerJ_j(k) = C(M+n, b)·C(γ+2n+1-b, γ-b)`
with `b = (γ+n+1+j)-k`; this is the V analogue of `ZhuVermaAnDescent19.Hker`, but the tower base is
`P+n+1+j` (carried by the *middle* binomial, the only `μ`-dependent factor) — not the reflected
`C(M+n,·)`. -/
noncomputable def VHkerJ (M n j : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) ((γ + (n : ℤ) + 1 + j) - k)
    * cbz (γ + 2 * (n : ℤ) + 1 - ((γ + (n : ℤ) + 1 + j) - k)) (γ - ((γ + (n : ℤ) + 1 + j) - k))

/-- **`VASum` as a `cbz(P+n+1+j, s+k)`-finsum** (V analogue of `ASum_eq_kFinsum`).  Reflect
`a ↦ (M+n)-a`, flip the middle binomial via `cbz_symm` (top `P+n+1+j` a `Nat`), and shift
`b = (γ+n+1+j)-k` to expose the kernel `VHkerJ` against `cbz(P+n+1+j, (μ+2n+2)+k)`. -/
theorem VASum_eq_kFinsum (M P n j : ℕ) (γ μ : ℤ) :
    VASum M P n j γ μ
      = ∑ᶠ k : ℤ, cbz ((P : ℤ) + n + 1 + j) (((μ : ℤ) + 2 * n + 2) + k) * VHkerJ M n j γ k := by
  rw [VASum]
  -- Reflect `a ↦ (M+n) - a`.
  rw [← Finset.sum_range_reflect
      (fun a => cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
          * cbz ((M : ℤ) + n) (a : ℤ)
          * cbz (γ + (n : ℤ) + 1 - M + a) (γ - M - n + a)) (M + n + 1)]
  rw [show (∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - ((M + n + 1 - 1 - a : ℕ) : ℤ))
                * cbz ((M : ℤ) + n) ((M + n + 1 - 1 - a : ℕ) : ℤ)
                * cbz (γ + (n : ℤ) + 1 - M + ((M + n + 1 - 1 - a : ℕ) : ℤ))
                    (γ - M - n + ((M + n + 1 - 1 - a : ℕ) : ℤ)))
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)
              * (cbz ((M : ℤ) + n) (a : ℤ)
                  * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from
      Finset.sum_congr rfl fun a ha => ?_]
  · -- range → `∑ᶠ a`, then flip the middle, then shift `a = (γ+n+1+j) - k`.
    rw [show (∑ a ∈ Finset.range (M + n + 1),
              cbz ((P : ℤ) + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)
                * (cbz ((M : ℤ) + n) (a : ℤ)
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
          = ∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from ?_]
    · -- flip the middle by `cbz_symm` (top `P+n+1+j` a `Nat`), exposing `+(s+...)` form.
      rw [show (∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
            = ∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1 + j)
                  (((μ : ℤ) + 2 * n + 2) + ((γ + (n : ℤ) + 1 + j) - a))
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from
        finsum_congr fun a => by
          rw [show ((P : ℤ) + n + 1 + j) = (((P + n + 1 + j : ℕ)) : ℤ) from by push_cast; ring,
            ZhuMu.cbz_symm (P + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)]
          congr 2
          push_cast; ring]
      -- shift `a = (γ+n+1+j) - k`  (`Equiv.subLeft (γ+n+1+j)`), identify with `VHkerJ k`.
      rw [← finsum_comp_equiv (Equiv.subLeft (γ + (n : ℤ) + 1 + j))
          (f := fun a : ℤ => cbz ((P : ℤ) + n + 1 + j)
                (((μ : ℤ) + 2 * n + 2) + ((γ + (n : ℤ) + 1 + j) - a))
              * (cbz ((M : ℤ) + n) a
                  * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))]
      simp only [Equiv.subLeft_apply]
      refine finsum_congr fun k => ?_
      rw [VHkerJ,
        show (γ + (n : ℤ) + 1 + j) - ((γ + (n : ℤ) + 1 + j) - k) = k from by ring]
    · -- range → `∑ᶠ`.
      refine (finsumZ_eq_range_sum (N := M + n + 1)
        (fun a : ℤ => cbz ((P : ℤ) + n + 1 + j) ((P : ℤ) - 2 * n - 2 - μ - γ + a)
            * (cbz ((M : ℤ) + n) a
                * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
        (fun p hp => by dsimp only; rw [cbz_apply_neg ((M : ℤ) + n) hp]; ring)
        (fun p hp => by
          dsimp only
          rw [cbz_lt (by positivity) (by
            have : (M + n + 1 : ℤ) ≤ p := by exact_mod_cast hp
            omega : (M : ℤ) + n < p)]; ring)).symm
  · -- the per-`a` reflected-summand rewrite.
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [show M + n + 1 - 1 - a = M + n - a from by omega]
    have hca : (((M + n - a : ℕ) : ℤ)) = (M : ℤ) + n - a := by rw [Nat.cast_sub hale]; push_cast; ring
    rw [hca]
    -- `cbz(M+n, M+n-a) = cbz(M+n, a)` via symmetry.
    rw [show cbz ((M : ℤ) + n) ((M : ℤ) + n - a)
          = cbz ((M : ℤ) + n) (a : ℤ) from by
        rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring,
          ← ZhuMu.cbz_symm (M + n) (a : ℤ)]]
    rw [show ((M : ℤ) + P - n - 2 - μ - γ) - ((M : ℤ) + n - a)
          = (P : ℤ) - 2 * n - 2 - μ - γ + a from by ring,
      show γ + (n : ℤ) + 1 - M + ((M : ℤ) + n - a) = γ + 2 * (n : ℤ) + 1 - a from by ring,
      show γ - M - n + ((M : ℤ) + n - a) = γ - a from by ring]
    ring

/-! ## Top-split the middle binomial to base `P+n`, exposing `GvJ`. -/

/-- The base-`P+n` per-`(j,k')` kernel: `GvJ_j(k') = ∑_t C(1+j, t)·VHkerJ_j(k'+t)`, obtained from
the Vandermonde top-split `C(P+n+1+j, s+k) = ∑_t C(1+j,t)·C(P+n, (s+k)-t)` of the `μ`-carrying
middle binomial.  M-dependent, P-independent. -/
noncomputable def GvJ (M n j : ℕ) (γ : ℤ) (kp : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (1 + j + 1), cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ (kp + t)

/-- `VHkerJ` vanishes below `n+1+j` (the `C(γ+2n+1-b, γ-b)` factor: `b = γ+n+1+j-k > γ`). -/
theorem VHkerJ_lo (M n j : ℕ) (γ : ℤ) {k : ℤ} (hk : k < (n : ℤ) + 1 + j) :
    VHkerJ M n j γ k = 0 := by
  rw [VHkerJ]
  -- `γ - b < 0` where `b = (γ+n+1+j) - k`; here `b > γ` ⇔ `k < n+1+j`.
  rw [cbz_apply_neg (γ + 2 * (n : ℤ) + 1 - ((γ + (n : ℤ) + 1 + j) - k))
    (by omega : γ - ((γ + (n : ℤ) + 1 + j) - k) < 0), mul_zero]

/-- `VHkerJ` vanishes above `γ+n+1+j` (the `C(M+n, γ+n+1+j-k)` factor: lower index `< 0`). -/
theorem VHkerJ_hi (M n j : ℕ) (γ : ℤ) {k : ℤ} (hk : γ + (n : ℤ) + 1 + j < k) :
    VHkerJ M n j γ k = 0 := by
  rw [VHkerJ, cbz_apply_neg ((M : ℤ) + n) (by omega), zero_mul]

/-- **`VInnerI` as a base-`P+n` finsum.**  Top-split `C(P+n+1+j, s+k)` into the grade-`P+n` carrier
and assemble `GvJ`. -/
theorem VInnerI_eq_GvJFinsum (M P n j : ℕ) (γ μ : ℤ) :
    VInnerI M P n j γ μ
      = ∑ᶠ kp : ℤ, cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp) * GvJ M n j γ kp := by
  rw [VInnerI_eq_VASum, VASum_eq_kFinsum]
  -- Top-split each `C(P+n+1+j, s+k)` via the Vandermonde `C((1+j)+(P+n), x) = ∑ᶠ t C(1+j,t) C(P+n, x-t)`.
  have hsplit : ∀ k : ℤ,
      cbz ((P : ℤ) + n + 1 + j) (((μ : ℤ) + 2 * n + 2) + k)
        = ∑ᶠ t : ℤ, cbz (1 + (j : ℤ)) t * cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t) := by
    intro k
    rw [show (P : ℤ) + n + 1 + j = (1 + (j : ℤ)) + ((P : ℤ) + n) from by ring,
      ← cbz_vandermonde (1 + (j : ℤ)) ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k), cbzConvol]
  -- Rewrite each `C(P+n+1+j, s+k)·VHkerJ(k)` as the finite `∑_{t∈range(1+j+1)}` of the split terms.
  rw [show (∑ᶠ k : ℤ, cbz ((P : ℤ) + n + 1 + j) (((μ : ℤ) + 2 * n + 2) + k) * VHkerJ M n j γ k)
        = ∑ᶠ k : ℤ, ∑ t ∈ Finset.range (1 + j + 1),
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k) from
      finsum_congr fun k => by
        rw [hsplit k, finsum_mul,
          finsumZ_eq_range_sum (N := 1 + j + 1)
            (fun t : ℤ => cbz (1 + (j : ℤ)) t * cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
                * VHkerJ M n j γ k)
            (fun p hp => by dsimp only; rw [cbz_apply_neg (1 + (j : ℤ)) hp, zero_mul, zero_mul])
            (fun p hp => by
              dsimp only
              rw [cbz_lt (by positivity) (by
                have : (1 + j + 1 : ℤ) ≤ p := by exact_mod_cast hp
                omega : 1 + (j : ℤ) < p), zero_mul, zero_mul])]
        refine Finset.sum_congr rfl fun t _ => by ring]
  -- Pull the finite `t`-sum outside the `∑ᶠ k`, reindex `k = kp + t` per `t`, then re-collect.
  rw [show (∑ᶠ k : ℤ, ∑ t ∈ Finset.range (1 + j + 1),
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k))
        = ∑ t ∈ Finset.range (1 + j + 1), ∑ᶠ k : ℤ,
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k) from by
      rw [← sum_finsum_comm (Finset.range (1 + j + 1))
          (fun t k => cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k))
          (fun t _ => ?_)]
      -- finite support of each per-`t` finsum in `k`.
      apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1 + j) (γ + (n : ℤ) + 1 + j))
      intro k hk
      rw [Function.mem_support] at hk
      rw [Set.mem_Icc]
      by_contra hcon
      apply hk
      simp only []
      rcases not_and_or.mp hcon with h | h
      · rw [VHkerJ_lo M n j γ (by omega : k < (n : ℤ) + 1 + j), mul_zero, mul_zero]
      · rw [VHkerJ_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < k), mul_zero, mul_zero]]
  -- Per `t`, reindex `k = kp + t` (so `(s+k)-t = s+kp`).
  rw [show (∑ t ∈ Finset.range (1 + j + 1), ∑ᶠ k : ℤ,
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k))
        = ∑ t ∈ Finset.range (1 + j + 1), ∑ᶠ kp : ℤ,
            cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
              * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ (kp + (t : ℤ))) from
      Finset.sum_congr rfl fun t _ => by
        rw [← finsum_comp_equiv (Equiv.addRight (t : ℤ))
            (f := fun k : ℤ => cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
                * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ k))]
        simp only [Equiv.coe_addRight]
        refine finsum_congr fun kp => by
          rw [show (((μ : ℤ) + 2 * n + 2) + (kp + (t : ℤ))) - t = ((μ : ℤ) + 2 * n + 2) + kp from by ring]]
  -- Swap the finite `t`-sum back inside, assemble `GvJ`.
  have hfin : ∀ t ∈ Finset.range (1 + j + 1),
      Function.HasFiniteSupport (fun kp : ℤ => cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
          * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ (kp + (t : ℤ)))) := by
    intro t _
    apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1 + j - t) (γ + (n : ℤ) + 1 + j - t))
    intro kp hkp
    rw [Function.mem_support] at hkp
    rw [Set.mem_Icc]
    by_contra hcon
    apply hkp
    rcases not_and_or.mp hcon with h | h
    · rw [VHkerJ_lo M n j γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1 + j), mul_zero, mul_zero]
    · rw [VHkerJ_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < kp + (t : ℤ)), mul_zero, mul_zero]
  rw [sum_finsum_comm (Finset.range (1 + j + 1))
      (fun t kp => cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
          * (cbz (1 + (j : ℤ)) (t : ℤ) * VHkerJ M n j γ (kp + (t : ℤ)))) hfin]
  refine finsum_congr fun kp => ?_
  rw [GvJ, Finset.mul_sum]

/-! ## The per-`j` tower collapse and the final V-core identity. -/

/-- For `γ < 0` the kernel `VHkerJ` vanishes identically: the two `cbz` factors have disjoint
support (`k ≤ γ+n+1+j < n+1+j ≤ k`). -/
theorem VHkerJ_gneg (M n j : ℕ) {γ : ℤ} (hγ : γ < 0) (k : ℤ) : VHkerJ M n j γ k = 0 := by
  rw [VHkerJ]
  rcases le_or_gt k (γ + (n : ℤ) + 1 + j) with hk | hk
  · -- second factor: `γ - b < 0` (here `b = (γ+n+1+j)-k`, and `k ≤ γ+n+1+j < n+1+j`).
    rw [cbz_apply_neg (γ + 2 * (n : ℤ) + 1 - ((γ + (n : ℤ) + 1 + j) - k))
      (by omega : γ - ((γ + (n : ℤ) + 1 + j) - k) < 0), mul_zero]
  · -- first factor's lower index `(γ+n+1+j)-k < 0`.
    rw [cbz_apply_neg ((M : ℤ) + n) (by omega : (γ + (n : ℤ) + 1 + j) - k < 0), zero_mul]

/-- `GvJ` vanishes for `kp < 0`: each `VHkerJ(kp+t)` with `t ≤ 1+j` has `kp+t < 1+j ≤ n+1+j`, below
the kernel's support floor (`VHkerJ_lo`). -/
theorem GvJ_lo (M n j : ℕ) (γ : ℤ) {kp : ℤ} (hkp : kp < 0) : GvJ M n j γ kp = 0 := by
  rw [GvJ]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (t : ℤ) ≤ 1 + (j : ℤ) := by
    have := Finset.mem_range.mp ht; exact_mod_cast (by omega : t ≤ 1 + j)
  rw [VHkerJ_lo M n j γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1 + j), mul_zero]

theorem GvJ_hi (M n j : ℕ) (γ : ℤ) (hjn : j ≤ n) {kp : ℤ} (hkp : 2 * (n : ℤ) + 2 + γ ≤ kp) :
    GvJ M n j γ kp = 0 := by
  rw [GvJ]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (t : ℤ) ≤ 1 + (j : ℤ) := by
    have := Finset.mem_range.mp ht; exact_mod_cast (by omega : t ≤ 1 + j)
  have hjn' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjn
  rw [VHkerJ_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < kp + (t : ℤ)), mul_zero]

/-- The per-`j` V tower weight (the `tower_swap` weight at base `P+n`):
`vtJ(δ) = ∑_{kp<Δ} (-1)^(kp-δ)·C(kp,δ)·GvJ(kp)`.  M-dependent, P-independent. -/
noncomputable def vtJ (M n j : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ kp ∈ Finset.range (2 * n + 2 + γ).toNat,
    (-1 : ℂ) ^ (kp - ν) * cbz (kp : ℤ) (ν : ℤ) * GvJ M n j γ (kp : ℤ)

/-- **Per-`j` `VInnerI` tower collapse** (grade `P`).  Via `VInnerI_eq_GvJFinsum` and `tower_swap`
(base `P+n`, support `[0,Δ_V)` from `GvJ_lo`/`GvJ_hi`). -/
theorem VInnerI_tower (M P n j : ℕ) (γ μ : ℤ) (hjn : j ≤ n) :
    VInnerI M P n j γ μ
      = ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
          vtJ M n j γ ν * cbz ((P : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) := by
  rw [VInnerI_eq_GvJFinsum]
  rw [show (∑ᶠ kp : ℤ, cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp) * GvJ M n j γ kp)
        = ∑ᶠ kp : ℤ, cbz (((P + n : ℕ)) : ℤ) (((μ : ℤ) + 2 * n + 2) + kp) * GvJ M n j γ kp from by
      push_cast; rfl]
  rw [tower_swap (P + n) (μ + 2 * n + 2) (GvJ M n j γ) (2 * n + 2 + γ).toNat
      (fun k hk => GvJ_lo M n j γ hk)
      (fun k hk => GvJ_hi M n j γ hjn (by
        have hh : ((2 * n + 2 + γ).toNat : ℤ) ≤ k := hk
        rcases lt_or_ge (2 * (n : ℤ) + 2 + γ) 0 with h | h
        · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
        · rw [Int.toNat_of_nonneg h] at hh; omega))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [vtJ]
  congr 2

/-- **The depth-`n` V-core weights** `wV(M,n,γ,δ) = ∑_{j≤n} (-1)^j C(j+n,j)·vtJ(M,n,j,γ,δ)`, the FZ
`j`-sum of the per-`j` grade-`P` tower weights.  Unlike the U-core's `wU`, the V weights depend on
`M` (the grade-`P` tower's basis `cbz(P+n+δ, μ+2n+2+δ)` is `M`-independent, so the residual
`M`-dependence of `VgammaModeColl` lives in the weights — the `C(M+n, …)` factor of `VHkerJ`); they
are `P`- and `μ`-independent. -/
noncomputable def wV (M n : ℕ) (γ : ℤ) (δ : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * vtJ M n j γ δ

/-- **The depth-`n` V-core scalar collapse** (Zhu Thm 2.1.2 / Frenkel–Zhu, V mirror of
`UgammaModeColl_eq_towerCoeff`).  Under the grade witness `hG`, the collected per-`(γ,μ)` V-side
scalar `VgammaModeColl` equals the grade-`P` `towerCoeff` tower with the `M`-dependent (but `P`- and
`μ`-independent) weights `wV` and depth `Δ_V = (2n+2+max γ 0).toNat`.  For `γ < 0` both sides vanish
(the `directVCoeff''` guard `if 0 ≤ γ` on the LHS; every `wV` weight vanishes via `VHkerJ_gneg`). -/
theorem VgammaModeColl_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeColl M P n G γ μ
      = towerCoeff P n (wV M n γ) (2 * n + 2 + max γ 0).toNat μ := by
  rw [VgammaModeColl_eq_jSum M P n G hG γ μ, towerCoeff]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, show max γ 0 = γ from by omega]
    -- expand each `VInnerI` into its grade-`P` tower, swap `j ↔ ν`, assemble `wV`.
    rw [show ∑ j ∈ Finset.range (n + 1),
              (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * VInnerI M P n j γ μ
          = ∑ j ∈ Finset.range (n + 1), ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * vtJ M n j γ ν)
                * cbz ((P : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) from
        Finset.sum_congr rfl fun j hj => by
          rw [VInnerI_tower M P n j γ μ (by have := Finset.mem_range.mp hj; omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => by ring,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [wV, Finset.sum_mul]
  · -- `γ < 0`: LHS `if`-branch is `0`; the tower depth `Δ_V = (2n+2+max γ 0).toNat`.
    rw [if_neg hγ, show max γ 0 = 0 from by omega]
    -- `2n+2+0 = 2n+2 > 0`, so the tower is NOT empty.  But each `wV` weight references `vtJ` whose
    -- `GvJ` carries the `if 0≤γ` guard *only through* `VHkerJ`'s `C(γ+2n+1-b, γ-b)` — for `γ<0`
    -- that vanishes, so every `wV` weight is `0`.
    symm
    refine Finset.sum_eq_zero fun δ _ => ?_
    rw [show wV M n γ δ = 0 from ?_, zero_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show vtJ M n j γ δ = 0 from ?_, mul_zero]
    refine Finset.sum_eq_zero fun kp _ => ?_
    rw [show GvJ M n j γ kp = 0 from ?_, mul_zero]
    rw [GvJ]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [VHkerJ_gneg M n j (by omega : γ < 0) (kp + (t : ℤ)), mul_zero]

end VOA
