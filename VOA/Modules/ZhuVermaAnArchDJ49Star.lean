/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ49Master
import VOA.Modules.ZhuVermaAnArchDJ24Gen
import VOA.Modules.ZhuVermaAnArchAnmFull

/-!
# Dong–Jiang Lemma 4.9 — the pure-`𝒱` statement `(★)` and its coefficient machinery

The `ℓ ≥ 0` half of `ModuleIterate` is free (`moduleIterate_nonneg`), so all of Dong–Jiang Lemma 4.9
sits in the regime `ℓ < 0`.  `ZhuVermaAnArchDJ49Iterate` shows that this regime, for **every**
`A(𝒱)`-module `U` simultaneously, follows from one statement about `𝒱` alone:

**`(★)` (`DJ49Star`)** — for homogeneous `u ∈ 𝒱_K`, `v ∈ 𝒱_M`, source level `n`, `ℓ < 0`, `N : ℤ`
and the common target level `q = K + M − ℓ − N − 2 + n`,

```
  u₍ℓ₎v − ∑ᵢ (−1)ⁱC(ℓ,i)·(u *^q_{n,pᵢ} v) + ∑ᵢ (−1)^{ℓ+i}C(ℓ,i)·(v *^q_{n,p'ᵢ} u) ∈ O_{q,n}(𝒱),
```

with `pᵢ = M−N−i−1+n` and `p'ᵢ = K−i−1+n` (both sums finite).

This file states `(★)` and proves the machinery that turns it into a **pure scalar** question about
generalized binomial coefficients — i.e. everything except the closed evaluation of the two
coefficient sums.  Concretely:

* `anmGenZ` — `anmGen` with an integer intermediate level (`0` at a negative level), the bookkeeping
  device that makes both sums in `(★)` index-free;
* `resFull_offdiag_mem_Onm` — **the leftover killer**: `Res_z (1+z)^{K+n}/z^{q+n+2+k} Y(u,z)v ∈
  O'_{q,n}` for every `k : ℕ` (Dong–Jiang Lemma 2.4 at general base level, `s = 0`);
* `coeffFinsum_offdiag_mem_Onm` — the same statement read **coefficientwise**: any `u`-mode series
  whose coefficient function is a finite combination of `j ↦ C(K+n, j+q+n+2+k)` lies in `O'_{q,n}`.
  This is exactly the shape in which the master identity's leftover appears;
* `anmGen_eq_coeff` — the **A-part expansion**: `u *^q_{n,p} v` written as an explicit `u`-mode
  series `∑ⱼ coefA(j)·u₍ⱼ₎v`, with `coefA(j) = ∑ₛ C(−a−1,s)·C(K+n, j+a+s+1)`, `a = n+q−p`
  (the `(−1)^s C(a+s,s) = C(−a−1,s)` step is the proved `alt_cbz_eq`);
* `anmGen_swap_coeff_mem` — the **B-part expansion**: `v *^q_{n,p} u` written, *modulo* `O'_{q,n}`,
  as a `u`-mode series, via the residue form of skew symmetry `resHom_skew_mod_Onm`;
* `dj49_generator_form` — the proved master identity `dj49_master` reindexed `r ↦ k* − k` into
  exactly the generator basis `j ↦ C(K+n, j+q+n+2+k)` that `coeffFinsum_offdiag_mem_Onm` kills.

## Engine verification of the statement itself (verify-before-formalize)

`(★)` was checked **in the exact form stated below** on the rank-1 free boson (Heisenberg VOA),
`SMAX = 10`, with exact-rational linear algebra: `u, v ∈ {𝟙, a₋₁𝟙, a₋₂𝟙, a₋₁a₋₁𝟙}`, `n ∈ {0,1,2}`,
`ℓ ∈ {−5,…,−1}`, `q ∈ {0,1,2,3}` and `N = K+M−ℓ−2+n−q` — **960 points, zero genuine failures**
(4 apparent failures at the extreme corner `K = M = 2, n = 0, ℓ = −5, q = 0` were artifacts of a
too-small generating slice of the ideal and all pass once the slice reaches the top grade `8` of the
tested element).  Membership held throughout modulo the **prime** summand `O'_{q,n}` alone, which is
why `DJ49StarPrime` (below) is recorded as the sharper sufficient target.

## What is NOT proved here

`DJ49Star W` itself.  After `anmGen_eq_coeff` and `anmGen_swap_coeff_mem` two things remain:
**(i)** the interchange of the outer `i`-summation of `(★)` with the inner `j`-summation of the two
expansions (both finite, but the interchange is not written here); and **(ii)** the genuinely open
scalar statement, that the `i`-weighted combination of the two coefficient functions above equals
`δ_{j,ℓ}` minus a finite combination of the generators `j ↦ C(K+n, j+q+n+2+k)`.  Engine-verified
(315,014 exact points, zero failures) with the closed form
`Δ(j) = ∑_{r=0}^{k*} (−1)^r C(K+n−1+r, r) C(K+n, j−ℓ−r)`, `k* = −ℓ−q−n−2`, whose truncated
Vandermonde evaluation is the proved `dj49_master`; but the closed evaluation of the two coefficient
sums (in particular the sub-threshold tail of the A-part and the whole of the B-part) is **not**
formalized.  Nothing here is an axiom or a `sorry`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemmas 2.3, 2.4), §4 (Lemma 4.9); `ZhuVermaAnArchDJ49Master`
(`dj49_master`), `ZhuVermaAnArchDJ24Gen` (`resHom_offdiag_mem_Onm_gen`), `ZhuVermaAnArchResSkew`
(`resFull`, `resHom_eq_resFull`, `resHom_skew_mod_Onm`, `finsetSum_smul_resFull`),
`ZhuVermaAnArchDJ48` (`alt_cbz_eq`), `ZhuVermaAnArchAnmFull` (`anmGen`, `OnmFull`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The Dong–Jiang product at an integer intermediate level -/

/-- **`anmGen` with the intermediate level index promoted to `ℤ`.**  At a negative level the
corresponding composition of two `M(U)`-modes factors through a nonexistent graded piece, so the
value is `0`; at a nonnegative level it is the ordinary three-index product `*^n_{m,p}`. -/
noncomputable def anmGenZ (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (p : ℤ) (u v : 𝒱) : 𝒱 :=
  if 0 ≤ p then anmGen W n m p.toNat u v else 0

/-- At a level named by a natural number, `anmGenZ` is `anmGen`. -/
theorem anmGenZ_of_eq (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) {p : ℤ} {P : ℕ}
    (h : p = (P : ℤ)) (u v : 𝒱) : anmGenZ W n m p u v = anmGen W n m P u v := by
  subst h
  rw [anmGenZ, if_pos (by positivity), Int.toNat_natCast]

/-- At a negative level, `anmGenZ` vanishes. -/
theorem anmGenZ_of_neg (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) {p : ℤ} (h : p < 0) (u v : 𝒱) :
    anmGenZ W n m p u v = 0 := by
  rw [anmGenZ, if_neg (not_le.mpr h)]

/-! ## §2  The pure-`𝒱` statement `(★)` of Dong–Jiang Lemma 4.9 -/

/-- **`(★)` — the pure-`𝒱` membership behind Dong–Jiang Lemma 4.9.**

For homogeneous `u ∈ 𝒱_K`, `v ∈ 𝒱_M`, source level `n`, mode `ℓ < 0`, mode `N`, and the common
target level `q = K + M − ℓ − N − 2 + n`:

```
  u₍ℓ₎v − ∑ᵢ (−1)ⁱC(ℓ,i)·(u *^q_{n,M−N−i−1+n} v) + ∑ᵢ (−1)^{ℓ+i}C(ℓ,i)·(v *^q_{n,K−i−1+n} u)
    ∈ O_{q,n}(𝒱).
```

This carries the whole content of DJ Lemma 4.9 (equivalently, of the `ℓ < 0` regime of
`ModuleIterate`); no module, tensor product or graded piece occurs in it. -/
def DJ49Star (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K M : ℕ) (u v : 𝒱), u ∈ W.grading (K : ℤ) → v ∈ W.grading (M : ℤ) →
    ∀ (n q : ℕ) (ℓ N : ℤ), ℓ < 0 → (q : ℤ) = (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ) →
      W.smul u ℓ v
          - ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
              (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
                - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)
        ∈ OnmFull W q n

/-- **`(★)` sharpened to the prime ideal `O'_{q,n} = Onm W q n`.**  Engine evidence (rank-1 free
boson, `SMAX = 10`, 960 exact points, zero genuine failures — see the module docstring) says the
membership in `(★)` in fact already holds modulo the *prime* summand `O'_{q,n}`, which is strictly
smaller than the full Dong–Jiang ideal `O_{q,n}`.  It is therefore enough to prove this version. -/
def DJ49StarPrime (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (K M : ℕ) (u v : 𝒱), u ∈ W.grading (K : ℤ) → v ∈ W.grading (M : ℤ) →
    ∀ (n q : ℕ) (ℓ N : ℤ), ℓ < 0 → (q : ℤ) = (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ) →
      W.smul u ℓ v
          - ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
              (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
                - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)
        ∈ Onm W q n

/-- The prime-ideal form of `(★)` implies `(★)`, since `O'_{q,n} ≤ O_{q,n}`. -/
theorem dj49Star_of_prime (W : VertexOperatorAlgebra 𝒱) (h : DJ49StarPrime W) : DJ49Star W :=
  fun K M u v hu hv n q ℓ N hℓ hq => Onm_le_OnmFull W q n (h K M u v hu hv n q ℓ N hℓ hq)

/-! ## §3  The leftover killer: off-diagonal residues lie in the ideal -/

/-- **Dong–Jiang Lemma 2.4 at general base level, in `resFull` form.**  For homogeneous `u ∈ 𝒱_K`
and every `k : ℕ`,

  `Res_z (1+z)^{K+n} / z^{q+n+2+k} Y(u,z)v ∈ O'_{q,n}(𝒱)`.

Every generator produced by the master identity of Lemma 4.9 has pole order `≥ q+n+2`, so this
single family annihilates the whole leftover. -/
theorem resFull_offdiag_mem_Onm (W : VertexOperatorAlgebra 𝒱) (q n : ℕ) {K : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (v : 𝒱) (k : ℕ) :
    resFull W ((K : ℤ) + (n : ℤ)) ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ)) u v ∈ Onm W q n := by
  have h := resHom_offdiag_mem_Onm_gen W q n hu v (Nat.zero_le k)
  rw [show ((n : ℤ) + ((0 : ℕ) : ℤ)) = ((n : ℕ) : ℤ) from by push_cast; ring] at h
  rwa [resHom_eq_resFull W hu ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ)) v] at h

/-- A finite `ℂ`-combination of the off-diagonal residues still lies in `O'_{q,n}`. -/
theorem finsetSum_resFull_offdiag_mem_Onm (W : VertexOperatorAlgebra 𝒱) (q n : ℕ) {K : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (v : 𝒱) (S : Finset ℕ) (c : ℕ → ℂ) :
    (∑ k ∈ S, c k • resFull W ((K : ℤ) + (n : ℤ)) ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ)) u v)
      ∈ Onm W q n :=
  Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (resFull_offdiag_mem_Onm W q n hu v k)

/-- **The leftover killer, coefficientwise.**  A `u`-mode series whose coefficient function is a
finite combination of the generators `j ↦ C(K+n, j+q+n+2+k)` lies in `O'_{q,n}(𝒱)`.  This is exactly
the shape in which the leftover of the Dong–Jiang Lemma 4.9 master identity appears. -/
theorem coeffFinsum_offdiag_mem_Onm (W : VertexOperatorAlgebra 𝒱) (q n : ℕ) {K : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (v : 𝒱) (S : Finset ℕ) (c : ℕ → ℂ) :
    (∑ᶠ j : ℤ, (∑ k ∈ S, c k * cbz ((K : ℤ) + (n : ℤ)) (j + ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ))))
        • W.smul u j v) ∈ Onm W q n := by
  rw [← finsetSum_smul_resFull W S c (fun _ : ℕ => (K : ℤ) + (n : ℤ))
    (fun k : ℕ => (q : ℤ) + (n : ℤ) + 2 + (k : ℤ)) u v]
  exact finsetSum_resFull_offdiag_mem_Onm W q n hu v S c

/-! ## §4  The A-part: `u *^q_{n,p} v` as an explicit `u`-mode series -/

/-- **The A-part expansion.**  For homogeneous `u ∈ 𝒱_K`, the Dong–Jiang product `u *^q_{n,p} v` is
the `u`-mode series with coefficient

  `coefA(j) = ∑_{s=0}^{p} C(−a−1, s)·C(K+n, j+a+s+1)`,   `a = n + q − p`,

the `(−1)^s C(a+s, s) = C(−a−1, s)` step being the proved `alt_cbz_eq` (upper-index negation).
This is the exact input of the Lemma 4.9 coefficient comparison. -/
theorem anmGen_eq_coeff (W : VertexOperatorAlgebra 𝒱) (q n p : ℕ) {K : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (v : 𝒱) :
    anmGen W q n p u v
      = ∑ᶠ j : ℤ, (∑ s ∈ Finset.range (p + 1),
          cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
            * cbz ((K : ℤ) + (n : ℤ)) (j + ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1)))
        • W.smul u j v := by
  have hstep : anmGen W q n p u v
      = ∑ s ∈ Finset.range (p + 1),
          cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
            • resFull W ((K : ℤ) + (n : ℤ))
                ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) u v := by
    rw [anmGen]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [resHom_eq_resFull W hu ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) v,
      alt_cbz_eq ((n : ℤ) + (q : ℤ) - (p : ℤ)) s]
  rw [hstep, finsetSum_smul_resFull W (Finset.range (p + 1))
    (fun s : ℕ => cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ))
    (fun _ : ℕ => (K : ℤ) + (n : ℤ))
    (fun s : ℕ => (n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) u v]

/-! ## §5  The B-part: `v *^q_{n,p} u` as a `u`-mode series, modulo the ideal -/

/-- **The B-part expansion.**  Modulo `O'_{q,n}(𝒱)`, the *swapped* Dong–Jiang product
`v *^q_{n,p} u` is a `u`-mode series with coefficient

  `coefB(j) = ∑_{s=0}^{p} C(−a−1,s)·(−1)^{a+s}·C(K+a+s−q−1, j+a+s+1)`,   `a = n + q − p`,

obtained from `alt_cbz_eq` together with the residue form of skew symmetry
(`resHom_skew_mod_Onm`, Dong–Jiang's `−z/(1+z)` contour move).  Note how the `(1+z)`-exponent
`K + P − q − 2` of each term now *depends on the pole order* `P = a+s+1`; this is what makes the
B-part genuinely harder than the A-part. -/
theorem anmGen_swap_coeff_mem (W : VertexOperatorAlgebra 𝒱) (q n p : ℕ) {K M : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ)) :
    anmGen W q n p v u
        - ∑ᶠ j : ℤ, (∑ s ∈ Finset.range (p + 1),
            cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
                * sgn ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1 + 1)
              * cbz ((K : ℤ) + ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) - (q : ℤ) - 2)
                  (j + ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1)))
            • W.smul u j v
      ∈ Onm W q n := by
  have hmem : ∀ s ∈ Finset.range (p + 1),
      cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
            • resHom W (n : ℤ) ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) v u
          - (cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
              * sgn ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1 + 1))
            • resFull W ((K : ℤ) + ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) - (q : ℤ) - 2)
                ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) u v
        ∈ Onm W q n := by
    intro s _
    have h := Submodule.smul_mem (Onm W q n)
      (cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ))
      (resHom_skew_mod_Onm W q n hu hv ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1))
    rwa [smul_sub, smul_smul] at h
  have h1 : anmGen W q n p v u
      = ∑ s ∈ Finset.range (p + 1),
          cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
            • resHom W (n : ℤ) ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) v u := by
    rw [anmGen]
    exact Finset.sum_congr rfl fun s _ => by
      rw [alt_cbz_eq ((n : ℤ) + (q : ℤ) - (p : ℤ)) s]
  rw [h1, ← finsetSum_smul_resFull W (Finset.range (p + 1))
    (fun s : ℕ => cbz (-((n : ℤ) + (q : ℤ) - (p : ℤ)) - 1) (s : ℤ)
      * sgn ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1 + 1))
    (fun s : ℕ => (K : ℤ) + ((n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) - (q : ℤ) - 2)
    (fun s : ℕ => (n : ℤ) + (q : ℤ) - (p : ℤ) + (s : ℤ) + 1) u v,
    ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ hmem

/-! ## §6  The master identity in the generator basis -/

/-- **The Dong–Jiang Lemma 4.9 master identity in the generator basis.**

Reindexing `dj49_master` by `r ↦ k* − k` turns the truncated alternating Vandermonde into a
combination of exactly the generators `j ↦ C(K+n, j+q+n+2+k)` that `coeffFinsum_offdiag_mem_Onm`
annihilates:

`δ_{j,ℓ} = ∑_{k=0}^{k*} (−1)^{k*−k}·C(K+n−1+k*−k, k*−k)·C(K+n, j+q+n+2+k)`   (`k* = −ℓ−q−n−2`,
`j − ℓ ≤ k*`).

Engine-verified in this exact form (5756/5756 exact sets, agreeing componentwise with an exact
`LinearSolve`). -/
theorem dj49_generator_form (K n q : ℕ) (hKn : 1 ≤ K + n) (ℓ : ℤ) (kstar : ℕ)
    (hk : (kstar : ℤ) = -ℓ - (q : ℤ) - (n : ℤ) - 2) (j : ℤ) (hj : j - ℓ ≤ (kstar : ℤ)) :
    (if j = ℓ then (1 : ℂ) else 0)
      = ∑ k ∈ Finset.range (kstar + 1),
          (-1 : ℂ) ^ (kstar - k) * (((K + n - 1 + (kstar - k)).choose (kstar - k) : ℕ) : ℂ)
            * cbz ((K : ℤ) + (n : ℤ)) (j + ((q : ℤ) + (n : ℤ) + 2 + (k : ℤ))) := by
  rw [← dj49_master K n hKn ℓ kstar j hj,
    ← Finset.sum_range_reflect (fun r : ℕ =>
      (-1 : ℂ) ^ r * (((K + n - 1 + r).choose r : ℕ) : ℂ)
        * cbz ((K : ℤ) + (n : ℤ)) (j - ℓ - (r : ℤ))) (kstar + 1)]
  refine Finset.sum_congr rfl fun k hkmem => ?_
  rw [Finset.mem_range] at hkmem
  have hle : k ≤ kstar := by omega
  have hidx : kstar + 1 - 1 - k = kstar - k := by omega
  rw [hidx]
  congr 2
  have hcast : ((kstar - k : ℕ) : ℤ) = (kstar : ℤ) - (k : ℤ) := by
    rw [Nat.cast_sub hle]
  omega

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmGenZ
  #print axioms VOA.anmGenZ_of_eq
  #print axioms VOA.anmGenZ_of_neg
  #print axioms VOA.dj49Star_of_prime
  #print axioms VOA.resFull_offdiag_mem_Onm
  #print axioms VOA.finsetSum_resFull_offdiag_mem_Onm
  #print axioms VOA.coeffFinsum_offdiag_mem_Onm
  #print axioms VOA.anmGen_eq_coeff
  #print axioms VOA.anmGen_swap_coeff_mem
  #print axioms VOA.dj49_generator_form
-/
