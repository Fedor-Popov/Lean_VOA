/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent18
import VOA.Modules.ZhuMuIdentity
import VOA.Modules.ZhuUCore

/-!
# The depth-`n` **U-core** scalar collapse `UgammaModeColl = towerCoeff M n (wU γ) Δ μ`.

This file proves the first of the two per-`(γ,μ)` scalar tower-collapses (the `HU` input of
`RightCircTowerEq_of_collapse`, `ZhuVermaAnDescent10`).  Over the engine-ready frame
`UgammaModeColl_eq_directSum''` (`ZhuVermaAnDescent18`), the collected U-side scalar collapses onto
the grade-`M` `towerCoeff` tower with EXPLICIT, `M`-independent weights `wU` and depth
`Δ = (2n+2+γ).toNat`.

## The verified collapse route (each step Mathematica-checked exact, `n ≤ 2`, `M,P ≤ 4`)

With `ℓ_i = i-2n-2`, `A = M+P+2n+1+j`, `K0 = M+P-n-2-μ-γ`:

* `ucore_guard` — the grade guard `0 ≤ M+P-ℓ_i-1` is ALWAYS true on the summation support `i ≤ M+n`.
* `UgammaModeColl_eq_jSum` — drop the guard, `(G i)+j = A-i`, factor the FZ index `j`:
  `UgammaModeColl = ∑_j (-1)^j cbz(j+n,j) · InnerI j`.
* **`InnerI_eq_ASum`** (R3): the inner `i`-sum collapses to an `a`-sum by the Vandermonde top-split
  `cbz(A-i, K0) = ∑_a cbz(M+n-i, a) cbz(P+n+1+j, K0-a)` (`vandermonde_range_top`) + trinomial symmetry
  (`trinom_symm`) + the per-`a` inner collapse `IC_collapse` (via `SR_collapse`).
* **`ASum_eq_kFinsum`** — reflect `a ↦ (M+n)-a` and shift `a = (μ+2n+2)+k`, exposing the
  `M`-INDEPENDENT kernel `Hker P n j γ k = cbz(P+n+1+j, k+P-γ)·cbz(2n+1+k, k)`.
* **`tower_swap`** (the generalized `mu_identity`/`inner_lemma` swap): a finitely-supported kernel
  `H` turns `∑ᶠ k, cbz(K, s+k)·H(k)` into the grade-`K` tower `∑_ν wt(ν)·cbz(K+ν, s+ν)`, weights
  `wt(ν) = ∑_k (-1)^{k-ν} cbz(k,ν) H(k)` (via `ZhuMu.inner_lemma`).  Hence **`InnerI_tower`**.
* **`UgammaModeColl_eq_towerCoeff`** — sum over `j` with `(-1)^j cbz(j+n,j)` to assemble the final
  `M`-independent weights `wU(P,n,γ,δ) = ∑_j (-1)^j cbz(j+n,j) wtJ(P,n,j,γ,δ)`.

The new reusable scalar lemmas `vandermonde_range_top`, `trinom_symm`, `SR_collapse`, `IC_collapse`,
`inner_lemma_range`, `tower_swap` are the depth-`n` analogues of the `ZhuUCore`/`ZhuMu` machinery and
serve the V-core (`ZhuVermaAnDescent20`) mirror as well.

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

/-! ## Step 0: the guard `0 ≤ M+P-(i-2n-2)-1` always holds for `i ≤ M+n`. -/

theorem ucore_guard (M P n i : ℕ) (hi : i ≤ M + n) :
    0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := by
  have : (i : ℤ) ≤ (M : ℤ) + n := by exact_mod_cast hi
  omega

/-! ## The inner `i`-sum (per fixed `j`). -/

/-- The inner `i`-sum at fixed FZ index `j`, with the middle binomial's top written as `A - i`
(`A = M+P+2n+1+j`) and the always-true guard dropped. -/
noncomputable def InnerI (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1),
    cbz ((M : ℤ) + n) (i : ℤ)
      * cbz (((M : ℤ) + P + 2 * n + 1 + j) - i) ((M : ℤ) + P - n - 2 - μ - γ)
      * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)

/-- **Step 1+2: structural reduction of `UgammaModeColl` to the `j`-sum of `InnerI`.**  Under the
grade witness `hG`, the always-true guard `ucore_guard` lets us drop the `if`, and `(G i)+j = A-i`.
-/
theorem UgammaModeColl_eq_jSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeColl M P n G γ μ
      = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * InnerI M P n j γ μ := by
  rw [UgammaModeColl_eq_directSum'' M P n G hG γ μ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [InnerI, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
  have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := ucore_guard M P n i hile
  rw [directUCoeff'', if_pos hgr, hG i hgr]
  -- now (G i)+j = M+P-(i-2n-2)-1+j; rewrite middle top to A - i
  have htop : ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) + (j : ℤ)
      = ((M : ℤ) + P + 2 * n + 1 + j) - i := by ring
  rw [htop]
  ring

/-! ## Reusable `cbz` lemmas. -/

/-- **Vandermonde range variant** keyed on the FIRST factor's top.  When the first top `m` is a
natural number `< N`, `∑_{a∈range N} C(m,a)·C(nn, k-a) = C(m+nn, k)` (the range covers the support
`[0,m]` of the first factor; the `cbz` `k<0` convention handles all other indices).  Unlike
`ZhuRes.vandermonde_range` (which needs `k < N`), this needs only `m < N`, useful when the lower
index `k` is unbounded. -/
theorem vandermonde_range_top (m : ℕ) (nn k : ℤ) {N : ℕ} (hm : m < N) :
    ∑ a ∈ Finset.range N, cbz (m : ℤ) (a : ℤ) * cbz nn (k - (a : ℤ)) = cbz ((m : ℤ) + nn) k := by
  rw [← cbz_vandermonde (m : ℤ) nn k, cbzConvol,
    finsumZ_eq_range_sum (N := N) (fun a : ℤ => cbz (m : ℤ) a * cbz nn (k - a))
      (fun p hp => by dsimp only; rw [cbz_apply_neg (m : ℤ) hp, zero_mul])
      (fun p hp => by
        dsimp only
        rw [cbz_lt (by positivity) (by
          have : (N : ℤ) ≤ p := hp
          have : (m : ℤ) < (N : ℤ) := by exact_mod_cast hm
          omega), zero_mul])]

/-- **Trinomial symmetry** (`K : ℕ`):  `C(K,i)·C(K-i,a) = C(K,a)·C(K-a,i)`.  Both equal
`C(K,i+a)·C(i+a,a)` via `ZhuUCore.trinomB` (using `ZhuMu.cbz_symm` on `C(i+a,a)=C(i+a,i)`). -/
theorem trinom_symm (K : ℕ) (i a : ℤ) :
    cbz (K : ℤ) i * cbz ((K : ℤ) - i) a = cbz (K : ℤ) a * cbz ((K : ℤ) - a) i := by
  rw [trinomB K i a, trinomB K a i, add_comm a i]
  rcases lt_or_ge (i + a) 0 with h | h
  · rw [cbz_apply_neg (K : ℤ) h, zero_mul, zero_mul]
  · obtain ⟨S, hS⟩ : ∃ S : ℕ, i + a = (S : ℤ) := ⟨(i + a).toNat, by omega⟩
    rw [hS, ZhuMu.cbz_symm S a, show (S : ℤ) - a = i from by omega]

/-- **The `SR` convolution.**  `∑_{i∈range N} C(Q,i)·C(-μ-1, i-c) = C(Q-μ-1, Q-c)` whenever the
range covers the support `[0,Q]` of the first factor (`Q < N`).  Proved by passing to `∑ᶠ`,
reflecting the index `i ↦ Q-i` (a ℤ-bijection) and `cbz_symm` (`Q` a Nat) into a genuine
convolution, then applying the Vandermonde. -/
theorem SR_collapse (Q : ℕ) (μ c : ℤ) {N : ℕ} (hQ : Q < N) :
    ∑ i ∈ Finset.range N, cbz (Q : ℤ) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - c)
      = cbz ((Q : ℤ) - μ - 1) ((Q : ℤ) - c) := by
  -- Pass the range sum to the full `∑ᶠ` (the first factor's support `[0,Q]` lies in `[0,N)`).
  rw [← finsumZ_eq_range_sum (N := N) (fun i : ℤ => cbz (Q : ℤ) i * cbz (-μ - 1) (i - c))
      (fun p hp => by dsimp only; rw [cbz_apply_neg (Q : ℤ) hp, zero_mul])
      (fun p hp => by
        dsimp only
        rw [cbz_lt (by positivity) (by
          have h1 : (N : ℤ) ≤ p := hp
          have h2 : (Q : ℤ) < (N : ℤ) := by exact_mod_cast hQ
          omega), zero_mul])]
  -- Reflect `i ↦ Q - i` (a ℤ-equiv), then `cbz_symm` turns the first factor into `C(Q, i)` and the
  -- second's lower index into `(Q - c) - i`, a genuine convolution.
  rw [← finsum_comp_equiv (Equiv.subLeft (Q : ℤ))
      (f := fun i : ℤ => cbz (Q : ℤ) i * cbz (-μ - 1) (i - c))]
  simp only [Equiv.subLeft_apply]
  rw [show (∑ᶠ i : ℤ, cbz (Q : ℤ) ((Q : ℤ) - i) * cbz (-μ - 1) (((Q : ℤ) - i) - c))
        = ∑ᶠ i : ℤ, cbz (Q : ℤ) i * cbz (-μ - 1) (((Q : ℤ) - c) - i) from
      finsum_congr fun i => by
        rw [← ZhuMu.cbz_symm Q i, show ((Q : ℤ) - i) - c = ((Q : ℤ) - c) - i from by ring]]
  rw [← cbzConvol, cbz_vandermonde]
  congr 1; ring

/-- **The per-`a` inner `i`-collapse** (the heart of R3).  For `a ≤ M+n`,
`∑_i C(M+n,i)·C(M+n-i,a)·C(-μ-1, i-2n-2-μ) = C(M+n,a)·C(M+n-a-μ-1, M-n-2-μ-a)`.  Via `trinom_symm`
(pull `C(M+n,a)` out of the first two factors) and `SR_collapse` on the remaining sum. -/
theorem IC_collapse (M n a : ℕ) (μ : ℤ) (ha : a ≤ M + n) :
    ∑ i ∈ Finset.range (M + n + 1),
        cbz ((M : ℤ) + n) (i : ℤ) * cbz ((M : ℤ) + n - (i : ℤ)) (a : ℤ)
          * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)
      = cbz ((M : ℤ) + n) (a : ℤ) * cbz ((M : ℤ) + n - (a : ℤ) - μ - 1) ((M : ℤ) - n - 2 - μ - a) := by
  -- `C(M+n, i)·C(M+n-i, a) = C(M+n, a)·C(M+n-a, i)`, then factor the `i`-independent `C(M+n,a)` out.
  rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring]
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M + n : ℕ) : ℤ) (i : ℤ) * cbz (((M + n : ℕ) : ℤ) - (i : ℤ)) (a : ℤ)
              * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)
        = cbz ((M + n : ℕ) : ℤ) (a : ℤ)
            * ∑ i ∈ Finset.range (M + n + 1),
                cbz (((M + n : ℕ) : ℤ) - (a : ℤ)) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [trinom_symm (M + n) (i : ℤ) (a : ℤ)]; ring]
  -- the remaining `i`-sum is `SR_collapse` with `Q = M+n-a`, `c = 2n+2+μ`.
  have hcast : ((M + n - a : ℕ) : ℤ) = (M : ℤ) + n - a := by rw [Nat.cast_sub ha]; push_cast; ring
  rw [show (∑ i ∈ Finset.range (M + n + 1),
            cbz (((M + n : ℕ) : ℤ) - (a : ℤ)) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - 2 * (n : ℤ) - 2 - μ))
        = ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M + n - a : ℕ) : ℤ) (i : ℤ) * cbz (-μ - 1) ((i : ℤ) - (2 * (n : ℤ) + 2 + μ)) from
      Finset.sum_congr rfl fun i _ => by
        rw [show ((M + n : ℕ) : ℤ) - (a : ℤ) = ((M + n - a : ℕ) : ℤ) from by rw [hcast]; push_cast; ring,
          show (i : ℤ) - 2 * (n : ℤ) - 2 - μ = (i : ℤ) - (2 * (n : ℤ) + 2 + μ) from by ring]]
  rw [SR_collapse (M + n - a) μ (2 * (n : ℤ) + 2 + μ) (N := M + n + 1) (by omega), hcast]
  congr 1
  push_cast
  ring_nf

/-! ## R3: `InnerI = ASum`. -/

/-- The `a`-sum (R3's RHS). -/
noncomputable def ASum (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range (M + n + 1),
    cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
      * cbz ((M : ℤ) + n) (a : ℤ)
      * cbz ((M : ℤ) + n - a - μ - 1) ((M : ℤ) - n - 2 - μ - a)

/-- **R3** (the verified inner-`i`-sum → `a`-sum collapse).  Expand the middle binomial
`C(A-i, K0)` by the Vandermonde top-split (`vandermonde_range_top`), swap to `a`-outer, factor the
`i`-independent `C(P+n+1+j, K0-a)`, and collapse each inner `i`-sum by `IC_collapse`. -/
theorem InnerI_eq_ASum (M P n j : ℕ) (γ μ : ℤ) :
    InnerI M P n j γ μ = ASum M P n j γ μ := by
  rw [InnerI, ASum]
  -- expand the middle factor into the `a`-sum.
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ)
              * cbz (((M : ℤ) + P + 2 * n + 1 + j) - i) ((M : ℤ) + P - n - 2 - μ - γ)
              * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)
        = ∑ i ∈ Finset.range (M + n + 1), ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
              * (cbz ((M : ℤ) + n) (i : ℤ) * cbz (((M : ℤ) + n) - (i : ℤ)) (a : ℤ)
                  * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)) from
      Finset.sum_congr rfl fun i hi => ?_]
  · -- swap and collapse each inner `i`-sum.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [← Finset.mul_sum, IC_collapse M n a μ hale]
    ring
  · -- the per-`i` middle expansion.
    have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
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

/-! ## The `k`-form of `ASum` (reflect `a ↦ M+n-a`, shift `a = s+k`). -/

/-- The (M-independent) per-`(j,k)` weight kernel `H_j(k) = C(P+n+1+j, k+P-γ)·C(2n+1+k, k)`. -/
noncomputable def Hker (P n j : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz ((P : ℤ) + n + 1 + j) (k + P - γ) * cbz (2 * (n : ℤ) + 1 + k) k

/-- The support of `fun a : ℤ => cbz(M+n, a)·Frefl(a)` lies in `[0, M+n]`; below we package the
reflected `ASum` as a `∑ᶠ` and shift `a = s + k`. -/
theorem ASum_eq_kFinsum (M P n j : ℕ) (γ μ : ℤ) :
    ASum M P n j γ μ
      = ∑ᶠ k : ℤ, cbz ((M : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k) * Hker P n j γ k := by
  rw [ASum]
  -- Reflect `a ↦ (M+n) - a`, rewriting each reflected summand to the clean form `cbz(M+n,b)·Frefl(b)`.
  rw [← Finset.sum_range_reflect
      (fun a => cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - a)
          * cbz ((M : ℤ) + n) (a : ℤ)
          * cbz ((M : ℤ) + n - a - μ - 1) ((M : ℤ) - n - 2 - μ - a)) (M + n + 1)]
  rw [show (∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + n + 1 + j) (((M : ℤ) + P - n - 2 - μ - γ) - ((M + n + 1 - 1 - a : ℕ) : ℤ))
                * cbz ((M : ℤ) + n) ((M + n + 1 - 1 - a : ℕ) : ℤ)
                * cbz ((M : ℤ) + n - ((M + n + 1 - 1 - a : ℕ) : ℤ) - μ - 1)
                    ((M : ℤ) - n - 2 - μ - ((M + n + 1 - 1 - a : ℕ) : ℤ)))
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (a : ℤ)
              * (cbz ((P : ℤ) + n + 1 + j) (((P : ℤ) - 2 * n - 2 - μ - γ) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)) from
      Finset.sum_congr rfl fun a ha => ?_]
  · -- now this range sum has support in `[0,M+n]`; convert to `∑ᶠ a`, then shift `a = s+k`.
    rw [show (∑ a ∈ Finset.range (M + n + 1),
              cbz ((M : ℤ) + n) (a : ℤ)
                * (cbz ((P : ℤ) + n + 1 + j) (((P : ℤ) - 2 * n - 2 - μ - γ) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))
          = ∑ᶠ a : ℤ, cbz ((M : ℤ) + n) a
                * (cbz ((P : ℤ) + n + 1 + j) (((P : ℤ) - 2 * n - 2 - μ - γ) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)) from ?_]
    · -- shift `a = s + k` (`Equiv.addLeft (μ+2n+2)`), then identify `Frefl(s+k) = Hker k`.
      rw [← finsum_comp_equiv (Equiv.addLeft ((μ : ℤ) + 2 * n + 2))
          (f := fun a : ℤ => cbz ((M : ℤ) + n) a
              * (cbz ((P : ℤ) + n + 1 + j) (((P : ℤ) - 2 * n - 2 - μ - γ) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))]
      simp only [Equiv.coe_addLeft]
      refine finsum_congr fun k => ?_
      rw [Hker,
        show ((μ : ℤ) + 2 * n + 2 + k) = (μ : ℤ) + 2 * (n : ℤ) + 2 + k from by ring,
        show ((P : ℤ) - 2 * n - 2 - μ - γ) + ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) = k + P - γ from by ring,
        show ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) - μ - 1 = 2 * (n : ℤ) + 1 + k from by ring,
        show ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) - 2 * n - 2 - μ = k from by ring]
    · -- range → `∑ᶠ`
      refine (finsumZ_eq_range_sum (N := M + n + 1)
        (fun a : ℤ => cbz ((M : ℤ) + n) a
            * (cbz ((P : ℤ) + n + 1 + j) (((P : ℤ) - 2 * n - 2 - μ - γ) + a)
                * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))
        (fun p hp => by dsimp only; rw [cbz_apply_neg ((M : ℤ) + n) hp, zero_mul])
        (fun p hp => by
          dsimp only
          rw [cbz_lt (by positivity) (by
            have : (M + n + 1 : ℤ) ≤ p := by exact_mod_cast hp
            omega), zero_mul])).symm
  · -- the per-`a` reflected-summand rewrite.
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [show M + n + 1 - 1 - a = M + n - a from by omega]
    have hca : (((M + n - a : ℕ) : ℤ)) = (M : ℤ) + n - a := by rw [Nat.cast_sub hale]; push_cast; ring
    rw [hca]
    -- `cbz(M+n, M+n-a) = cbz(M+n, a)` via symmetry (top `M+n` a Nat).
    rw [show cbz ((M : ℤ) + n) ((M : ℤ) + n - a)
          = cbz ((M : ℤ) + n) (a : ℤ) from by
        rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring,
          ← ZhuMu.cbz_symm (M + n) (a : ℤ)]]
    -- rewrite the other two lower/top indices.
    rw [show ((M : ℤ) + P - n - 2 - μ - γ) - ((M : ℤ) + n - a)
          = ((P : ℤ) - 2 * n - 2 - μ - γ) + a from by ring,
      show (M : ℤ) + n - ((M : ℤ) + n - a) - μ - 1 = (a : ℤ) - μ - 1 from by ring,
      show (M : ℤ) - n - 2 - μ - ((M : ℤ) + n - a) = (a : ℤ) - 2 * n - 2 - μ from by ring]
    ring

/-! ## The `inner_lemma`-driven tower swap. -/

/-- **`inner_lemma` extended to a fixed range `R`.**  For `k < R`,
`∑_{ν∈range R} (-1)^(k-ν)·C(k,ν)·C(K+ν, s+ν) = C(K, s+k)`.  (The terms `ν > k` carry `C(k,ν)=0`.) -/
theorem inner_lemma_range (K : ℕ) (s : ℤ) {R : ℕ} (k : ℕ) (hk : k < R) :
    ∑ ν ∈ Finset.range R,
        (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * cbz ((K : ℤ) + ν) (s + ν)
      = cbz (K : ℤ) (s + (k : ℤ)) := by
  rw [← ZhuMu.inner_lemma K k s]
  symm
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  · intro x hx hxni
    simp only [Finset.mem_range, not_lt] at hx hxni
    rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : k < x)), mul_zero, zero_mul]

/-- **The tower swap.**  If `H : ℤ → ℂ` is supported on `[0, R)`, then `∑ᶠ k, C(K,s+k)·H(k)`
collapses to the grade-`K` tower `∑_{ν<R} wt(ν)·C(K+ν, s+ν)` with the `M`-independent weights
`wt(ν) = ∑_{k<R} (-1)^(k-ν)·C(k,ν)·H(k)`.  Each `C(K,s+k)` is expanded by `inner_lemma_range`, then
the finite `(k,ν)`-sum is swapped. -/
theorem tower_swap (K : ℕ) (s : ℤ) (H : ℤ → ℂ) (R : ℕ)
    (hlo : ∀ k : ℤ, k < 0 → H k = 0) (hhi : ∀ k : ℤ, (R : ℤ) ≤ k → H k = 0) :
    (∑ᶠ k : ℤ, cbz (K : ℤ) (s + k) * H k)
      = ∑ ν ∈ Finset.range R,
          (∑ k ∈ Finset.range R, (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * H (k : ℤ))
            * cbz ((K : ℤ) + ν) (s + ν) := by
  -- pass the `∑ᶠ` to a range sum.
  rw [finsumZ_eq_range_sum (N := R) (fun k : ℤ => cbz (K : ℤ) (s + k) * H k)
      (fun p hp => by dsimp only; rw [hlo p hp, mul_zero])
      (fun p hp => by dsimp only; rw [hhi p hp, mul_zero])]
  -- expand each `C(K, s+k)` into the ν-tower, then swap.
  rw [show ∑ k ∈ Finset.range R, cbz (K : ℤ) (s + (k : ℤ)) * H (k : ℤ)
        = ∑ k ∈ Finset.range R, ∑ ν ∈ Finset.range R,
            (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * cbz ((K : ℤ) + ν) (s + ν) * H (k : ℤ) from
      Finset.sum_congr rfl fun k hk => by
        rw [← inner_lemma_range K s k (Finset.mem_range.mp hk), Finset.sum_mul],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

/-! ## Support of `Hker` and the per-`j` `InnerI` tower collapse. -/

/-- `Hker` vanishes for `k < 0` (the `C(2n+1+k, k)` factor). -/
theorem Hker_lo (P n j : ℕ) (γ : ℤ) {k : ℤ} (hk : k < 0) : Hker P n j γ k = 0 := by
  rw [Hker, cbz_apply_neg (2 * (n : ℤ) + 1 + k) hk, mul_zero]

/-- `Hker` vanishes for `2n+2+γ ≤ k` when `j ≤ n` (the `C(P+n+1+j, k+P-γ)` factor: top < lower). -/
theorem Hker_hi (P n j : ℕ) (γ : ℤ) (hjn : j ≤ n) {k : ℤ} (hk : 2 * (n : ℤ) + 2 + γ ≤ k) :
    Hker P n j γ k = 0 := by
  have hjn' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjn
  rw [Hker, cbz_lt (by positivity) (by omega : (P : ℤ) + n + 1 + j < k + P - γ), zero_mul]

/-- **Per-`j` `InnerI` tower collapse.**  `InnerI` is the grade-`M` tower
`∑_{ν<Δ} wtJ(ν)·C(M+n+ν, s+ν)` (`s = μ+2n+2`, `Δ = (2n+2+γ).toNat`) with the `M`-independent weights
`wtJ(ν) = ∑_{k<Δ} (-1)^(k-ν)·C(k,ν)·Hker(k)`.  Via `InnerI_eq_ASum`, `ASum_eq_kFinsum`, `tower_swap`. -/
noncomputable def wtJ (P n j : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (2 * n + 2 + γ).toNat,
    (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * Hker P n j γ (k : ℤ)

theorem InnerI_tower (M P n j : ℕ) (γ μ : ℤ) (hjn : j ≤ n) :
    InnerI M P n j γ μ
      = ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
          wtJ P n j γ ν * cbz ((M : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) := by
  rw [InnerI_eq_ASum, ASum_eq_kFinsum]
  rw [show (∑ᶠ k : ℤ, cbz ((M : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k) * Hker P n j γ k)
        = ∑ᶠ k : ℤ, cbz (((M + n : ℕ)) : ℤ) (((μ : ℤ) + 2 * n + 2) + k) * Hker P n j γ k from by
      push_cast; rfl]
  rw [tower_swap (M + n) (μ + 2 * n + 2) (Hker P n j γ) (2 * n + 2 + γ).toNat
      (fun k hk => Hker_lo P n j γ hk)
      (fun k hk => Hker_hi P n j γ hjn (by
        have hh : ((2 * n + 2 + γ).toNat : ℤ) ≤ k := hk
        rcases lt_or_ge (2 * (n : ℤ) + 2 + γ) 0 with h | h
        · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
        · rw [Int.toNat_of_nonneg h] at hh; omega))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [wtJ]
  congr 2

/-! ## The final U-core identity. -/

/-- **The depth-`n` U-core weights** `wU(P,n,γ,δ) = ∑_{j≤n} (-1)^j C(j+n,j)·wtJ(P,n,j,γ,δ)`,
the `M`-independent FZ `j`-sum of the per-`j` tower weights `wtJ`.  (`P`, `n` are fixed structural
data of the U-core; the weights are independent of the grade `M` and the mode `μ`.) -/
noncomputable def wU (P n : ℕ) (γ : ℤ) (δ : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * wtJ P n j γ δ

/-- **The U-core scalar collapse** (Zhu Thm 2.1.2 / Frenkel–Zhu, depth-`n`).  Under the grade
witness `hG`, the collected per-`(γ,μ)` U-side scalar `UgammaModeColl` equals the grade-`M`
`towerCoeff` tower with the explicit `M`-independent weights `wU` and depth `Δ = (2n+2+γ).toNat`. -/
theorem UgammaModeColl_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeColl M P n G γ μ
      = towerCoeff M n (wU P n γ) (2 * n + 2 + γ).toNat μ := by
  rw [UgammaModeColl_eq_jSum M P n G hG γ μ, towerCoeff]
  -- expand each `InnerI` into its tower, swap `j ↔ ν`, assemble `wU`.
  rw [show ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * InnerI M P n j γ μ
        = ∑ j ∈ Finset.range (n + 1), ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * wtJ P n j γ ν)
              * cbz ((M : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) from
      Finset.sum_congr rfl fun j hj => by
        rw [InnerI_tower M P n j γ μ (by have := Finset.mem_range.mp hj; omega), Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => by ring,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [wU, Finset.sum_mul]

end VOA
