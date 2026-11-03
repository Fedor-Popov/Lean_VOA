/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchABS
import VOA.Modules.ZhuVermaAnArchAnmIdeal
import VOA.Modules.ZhuVermaAnArchDJ22

/-!
# Dong–Jiang **Lemma 2.7** — the `O'''_{n,m}` level-mixing inclusion

This file formalizes Dong–Jiang, *Bimodules associated to vertex operator algebras*,
Math. Z. 259 (2008) 799–826 (`math/0601626`), **Lemma 2.7**:
> For `p₁, p₂, m, n ∈ ℤ₊`, `(V ∗ⁿ_{p₁,p₂} O'_{p₂,p₁}(V)) ∗ⁿ_{m,p₁} V ⊆ O_{n,m}(V)`.

In the repo's `OnmFull`/`anmGen` infrastructure the headline target is
```
levelMixGen_mem_OnmFull :
  anmGen W n m p₁ (anmGen W n p₁ p₂ a g) v ∈ OnmFull W n m     (g ∈ Onm W p₂ p₁)
```
i.e. `(a ∗ⁿ_{p₁,p₂} g) ∗ⁿ_{m,p₁} v ∈ O_{n,m}` for `g ∈ O'_{p₂,p₁}`.

## DJ's published proof (formalized faithfully here)

DJ first prove **the absorption step (DJ 2.7, lines 643–686)**: the *shifted* grading generator
`(L(−1)u + (L(0) + p₁ − p₂)u)` absorbed by the off-diagonal product `∗^{p₂}_{m,p₁}` collapses to a
scalar multiple of the circle generator:
```
(L(−1)u + (L(0) + p₁−p₂)u) ∗^{p₂}_{m,p₁} v
  = (−1)^{p₁} C(m+p₂, p₁) (m+p₂+1) · (u ∘^{p₂}_m v).
```
This is `anmLgen_shift_absorb` below — the genuine residue content of DJ 2.7, proved (mirroring the
diagonal `ZhuVermaAnArchABS.leftProd_Lgen_eq` and the `m = 0` `anmRight_zero_Lgen_eq`) by the
integration-by-parts telescope of the alternating `i`-sum.  Its scalar core
`anmShift_abs_scalar` is the exact off-diagonal analogue of `abs_scalar`/`anm_abs_scalar`,
verified symbolically (by an exploratory script, not retained; zero mismatches over `M,m,p₁,p₂ ≤ 6`, all modes).

The five-step set-inclusion reassociation chain (DJ 2.7, lines 697–712) then assembles the headline.
Each step is `Submodule.add_mem`/`span_le` bookkeeping over the `OnmFull` generators, consuming the
already-proven `anmCirc_mem_OnmFull`/`anmLgen_mem_OnmFull`/`assocDefect_mem_OnmFull`/
`levelMix_mem_OnmFull` and the absorption step above.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.7); Dong–Li–Mason,
J. Algebra 206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Integer-top `cbz` absorption / upper-shift lemmas.

The off-diagonal product `∗^{p₂}_{m,p₁}` carries binomials `C(m+p₂−p₁+i, i)` whose integer top
`m+p₂−p₁+i` may be negative; the diagonal `cbz_upper_shift` (`ℕ`-top) does not cover that.  We
provide the integer-top forms used by the absorption telescope. -/

/-- **Integer-top upper shift** `(k+1)·C(T+1, k+1) = (T+1)·C(T, k)` for `T : ℤ`, `k : ℕ`
(the `cbz_upper_shift` analogue valid for arbitrary integer top, via the falling product). -/
theorem cbz_upper_shift_int (T : ℤ) (k : ℕ) :
    ((k : ℂ) + 1) * cbz (T + 1) ((k : ℤ) + 1) = ((T : ℂ) + 1) * cbz T (k : ℤ) := by
  have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  -- clear `k!` from both sides
  refine mul_left_cancel₀ hfac ?_
  rw [cbz_apply_nonneg (T + 1) (by omega : (0 : ℤ) ≤ (k : ℤ) + 1),
      cbz_apply_nonneg T (by omega : (0 : ℤ) ≤ (k : ℤ)),
      show ((k : ℤ) + 1).toNat = k + 1 from by omega,
      show ((k : ℤ)).toNat = k from by omega]
  -- LHS · k! = (k+1)! · C(T+1,k+1) = ∏_{i<k+1}(T+1-i) = (T+1)·∏_{i<k}(T-i)
  have e1 := gBinom_mul_factorial (T + 1) (k + 1)
  have e2 := gBinom_mul_factorial T k
  rw [Nat.factorial_succ, Nat.cast_mul] at e1
  push_cast at e1 e2
  have hpeel : (∏ i ∈ Finset.range (k + 1), (((T : ℂ) + 1) - (i : ℂ)))
      = ((T : ℂ) + 1) * ∏ i ∈ Finset.range k, ((T : ℂ) - (i : ℂ)) := by
    rw [prod_falling_succ ((T : ℂ) + 1) k]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  rw [hpeel] at e1
  -- `e1 : ((k+1) * k!) * C(T+1,k+1) = (T+1) * ∏_{i<k}(T-i)`
  -- `e2 : k! * C(T,k) = ∏_{i<k}(T-i)`
  rw [← e2] at e1
  push_cast
  linear_combination e1

/-! ## The off-diagonal absorption scalar core (DJ 2.7 step a, per mode).

For homogeneous `u ∈ 𝒱_M`, the coefficient of `u₍ᵣ₎v` in `(L(−1)u+(L(0)+p₁−p₂)u) ∗^{p₂}_{m,p₁} v`
telescopes to the scalar multiple of the coefficient of `u₍ᵣ₎v` in `(m+p₂+1)/(scalar)·(u ∘^{p₂}_m v)`.
This is the exact off-diagonal generalization of `abs_ibp_coeff`/`abs_scalar`
(`ZhuVermaAnArch.lean`) and `anm_abs_scalar` (`ZhuVermaAnArchAnmIdeal.lean`). -/

/-- **The off-diagonal ABS integration-by-parts identity (per `i`).**  Writing
`A := C(M+m, r+m+p₂−p₁+i+1)`, `C := C(M+m, r+m+p₂−p₁+i+2)`, the per-`i` bracket of the absorbed
generator,
`(M+p₁−p₂)·A − (r+1)·C(M+1+m, r+m+p₂−p₁+i+2)`, equals `i·A + (m+p₂−p₁+i+1)·C`.
Reduces (after `cbz_pascal_up` on `C(M+1+m,·)`) to `cbz_absorption (M+m) (r+m+p₂−p₁+i+2)`. -/
theorem dj27_ibp_coeff (M m p₁ p₂ : ℕ) (i : ℕ) (r : ℤ) :
    ((M : ℂ) + (p₁ : ℂ) - (p₂ : ℂ))
        * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1)
      - ((r : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (r + m + p₂ - p₁ + i + 2)
      = (i : ℂ) * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1)
        + ((m : ℂ) + p₂ - p₁ + i + 1) * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 2) := by
  -- Pascal-up: C(M+1+m, t₂) = C(M+m, t₂) + C(M+m, t₂-1), t₂ = r+m+p₂-p₁+i+2.
  have hp : cbz ((M : ℤ) + 1 + m) (r + m + p₂ - p₁ + i + 2)
      = cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 2)
        + cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1) := by
    have h := cbz_pascal_up ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 2)
    rw [show ((M : ℤ) + m + 1) = (M : ℤ) + 1 + m from by ring,
        show (r + (m : ℤ) + p₂ - p₁ + i + 2 - 1) = r + m + p₂ - p₁ + i + 1 from by ring] at h
    exact h
  -- absorption with top (M+m : ℕ), index t₂ = r+m+p₂-p₁+i+2:
  --   C(M+m, t₂)·t₂ = C(M+m, t₂-1)·(M+m - t₂ + 1).
  have ha := cbz_absorption (M + m) (r + m + p₂ - p₁ + i + 2)
  rw [show (((M + m : ℕ) : ℤ)) = (M : ℤ) + m from by push_cast; ring,
      show (r + (m : ℤ) + p₂ - p₁ + i + 2 - 1) = r + m + p₂ - p₁ + i + 1 from by ring] at ha
  rw [hp]
  push_cast at ha ⊢
  linear_combination -ha

/-- **The off-diagonal ABS per-mode scalar identity.**  The alternating `i`-sum coefficient of
`u₍ᵣ₎v` in `(L(−1)u+(L(0)+p₁−p₂)u) ∗^{p₂}_{m,p₁} v` collapses to
`(−1)^{p₁} C(m+p₂, p₁) (m+p₂+1) · C(M+m, r+m+p₂+2)` (= scalar · coeff of the circle generator).
Proof: rewrite each `i`-bracket via `dj27_ibp_coeff`, then telescope with
`D i := (−1)ⁱ·i·C(m+p₂−p₁+i, i)·C(M+m, r+m+p₂−p₁+i+1)` — each summand `= D i − D(i+1)` by
`cbz_upper_shift_int`, so the sum is `D 0 − D(p₁+1) = −D(p₁+1)`; a final `cbz_upper_shift_int`
gives the scalar.  Exact off-diagonal analogue of `abs_scalar`. -/
theorem dj27_abs_scalar (M m p₁ p₂ : ℕ) (r : ℤ) :
    (∑ i ∈ Finset.range (p₁ + 1),
        (-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i *
          (((M : ℂ) + (p₁ : ℂ) - (p₂ : ℂ)) * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1)
            - ((r : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (r + m + p₂ - p₁ + i + 2)))
      = (-1 : ℂ) ^ p₁ * cbz ((m : ℤ) + p₂) p₁ * ((m : ℂ) + p₂ + 1)
          * cbz ((M : ℤ) + m) (r + m + p₂ + 2) := by
  set D : ℕ → ℂ := fun i =>
    (-1 : ℂ) ^ i * (i : ℂ) * cbz ((m : ℤ) + p₂ - p₁ + i) i
      * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1) with hD
  -- per-term: term_i = D_i - D_{i+1}.
  have hterm : ∀ i ∈ Finset.range (p₁ + 1),
      (-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i *
        (((M : ℂ) + (p₁ : ℂ) - (p₂ : ℂ)) * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 1)
          - ((r : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (r + m + p₂ - p₁ + i + 2)) = D i - D (i + 1) := by
    intro i _
    rw [dj27_ibp_coeff M m p₁ p₂ i r]
    -- link (i+1)·C(m+p₂−p₁+i+1, i+1) = (m+p₂−p₁+i+1)·C(m+p₂−p₁+i, i)
    have hsh := cbz_upper_shift_int ((m : ℤ) + p₂ - p₁ + i) i
    rw [show ((m : ℤ) + p₂ - p₁ + i + 1) = ((m : ℤ) + p₂ - p₁ + i) + 1 from by ring] at hsh
    push_cast at hsh
    simp only [hD]
    rw [show (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 from by push_cast; ring,
        show ((m : ℤ) + p₂ - p₁ + ((i : ℤ) + 1)) = ((m : ℤ) + p₂ - p₁ + i) + 1 from by ring,
        show (r + (m : ℤ) + p₂ - p₁ + ((i : ℤ) + 1) + 1) = r + m + p₂ - p₁ + i + 2 from by ring]
    push_cast [pow_succ]
    linear_combination (-((-1 : ℂ) ^ i * cbz ((M : ℤ) + m) (r + m + p₂ - p₁ + i + 2))) * hsh
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' D (p₁ + 1)]
  -- D 0 = 0, so the result is -D (p₁+1); apply cbz_upper_shift_int once more.
  have hsh := cbz_upper_shift_int ((m : ℤ) + p₂) p₁
  simp only [hD]
  rw [show (((p₁ + 1 : ℕ) : ℤ)) = (p₁ : ℤ) + 1 from by push_cast; ring,
      show ((m : ℤ) + p₂ - p₁ + ((p₁ : ℤ) + 1)) = ((m : ℤ) + p₂) + 1 from by ring,
      show (r + (m : ℤ) + p₂ - p₁ + ((p₁ : ℤ) + 1) + 1) = r + m + p₂ + 2 from by ring,
      show ((m : ℤ) + p₂ + 1) = ((m : ℤ) + p₂) + 1 from by ring] at *
  push_cast [pow_succ] at hsh ⊢
  linear_combination ((-1 : ℂ) ^ p₁ * cbz ((M : ℤ) + m) (r + m + p₂ + 2)) * hsh

/-! ## The off-diagonal vector absorption (DJ 2.7 step a, vector form).

We mirror the bar-product assembly `ZhuVermaAnArchDJ22.anmGenBar_Lgen_eq`, generalizing the inner
pole from `m+i+1` to the off-diagonal `m+p₂−p₁+i+1` and the binomial top from `m+i` to
`m+p₂−p₁+i`, and using the *shifted* grading generator `(L(−1)u + (L(0)+p₁−p₂)u)`. -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i − s)` onto `Icc Lo Hi` (mode `μ = i − s`), local copy. -/
private theorem reindexToIcc27 (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
    (hsub : Finset.Icc (-s) ((P : ℤ) - s) ⊆ Finset.Icc Lo Hi)
    (hzero : ∀ μ ∈ Finset.Icc Lo Hi, μ ∉ Finset.Icc (-s) ((P : ℤ) - s) → g (μ + s) = 0) :
    ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ μ ∈ Finset.Icc Lo Hi, g (μ + s) • T μ := by
  have h1 : ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ μ ∈ Finset.Icc (-s) ((P : ℤ) - s), g (μ + s) • T μ := by
    refine Finset.sum_nbij' (i := fun i => (i : ℤ) - s) (j := fun μ => (μ + s).toNat)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc]; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
    · intro a ha; simp only [Finset.mem_range] at ha; simp only []
      rw [show ((a : ℤ) - s + s) = (a : ℤ) by ring, Int.toNat_natCast]
    · intro a ha; simp only [Finset.mem_Icc] at ha; simp only []
      rw [Int.toNat_of_nonneg (by omega)]; ring
    · intro a ha; simp only [Finset.mem_range] at ha; simp only []
      refine congr_arg₂ _ ?_ ?_
      · ring
      · ring
  rw [h1, ← Finset.sum_subset hsub]
  intro μ hμ hμnot
  rw [hzero μ hμ hμnot, zero_smul]

/-- The `(L₋₁u)` summand of `∗^{p₂}_{m,p₁}`, per `i`, on the common mode range
`Icc (-(m+p₂+2)) (M-1)`.  After `smul_L_neg_one`, the inner sum becomes
`∑_μ (-(μ+1))·C(M+1+m, μ+m+p₂−p₁+i+2) • u₍μ₎v`. -/
private theorem Lneg_piece27 (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (i : ℕ) (hi : i ≤ p₁) :
    ∑ ℓ ∈ Finset.range (((M : ℤ) + 1 + (m : ℤ)).toNat + 1),
        cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ •
          W.smul (W.L (-1) u) ((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1)) v
      = ∑ μ ∈ Finset.Icc (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁),
          (-((μ : ℤ) + 1) * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 2))
            • W.smul u μ v := by
  have hstep : ∀ ℓ : ℕ,
      cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ •
          W.smul (W.L (-1) u) ((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1)) v
        = (cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ *
            (-((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1))))
            • W.smul u ((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1) - 1) v := by
    intro ℓ
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun ℓ _ => hstep ℓ)]
  have hmode : ∀ ℓ : ℤ,
      (ℓ - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1) - 1)
        = ℓ - ((m : ℤ) + p₂ - p₁ + i + 2) := by intro ℓ; ring
  simp only [hmode]
  rw [reindexToIcc27 (((M : ℤ) + 1 + (m : ℤ)).toNat) ((m : ℤ) + p₂ - p₁ + i + 2)
      (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁)
      (fun ℓ => cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ
        * (-(ℓ - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1))))
      (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [show (μ + ((m : ℤ) + p₂ - p₁ + i + 2)) = μ + m + p₂ - p₁ + i + 2 by ring]
    push_cast; ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hnot : ¬ (-((m : ℤ) + p₂ - p₁ + i + 2) ≤ μ
        ∧ μ ≤ (M : ℤ) + 1 + m - ((m : ℤ) + p₂ - p₁ + i + 2)) := hμnot
    rcases lt_or_ge μ (-((m : ℤ) + p₂ - p₁ + i + 2)) with hlo | hge
    · rw [cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (M : ℤ) + 1 + m - ((m : ℤ) + p₂ - p₁ + i + 2) < μ := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [cbz_lt (by positivity) (by omega), zero_mul]

/-- The `u` summand of `∗^{p₂}_{m,p₁}`, per `i`, on the common mode range:
`∑_μ C(M+m, μ+m+p₂−p₁+i+1) • u₍μ₎v`. -/
private theorem u_piece27 (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (i : ℕ) (hi : i ≤ p₁) :
    ∑ ℓ ∈ Finset.range (((M : ℤ) + (m : ℤ)).toNat + 1),
        cbz ((M : ℤ) + (m : ℤ)) ℓ •
          W.smul u ((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1)) v
      = ∑ μ ∈ Finset.Icc (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁),
          cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1) • W.smul u μ v := by
  rw [reindexToIcc27 (((M : ℤ) + (m : ℤ)).toNat) ((m : ℤ) + p₂ - p₁ + i + 1)
      (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁)
      (fun ℓ => cbz ((M : ℤ) + (m : ℤ)) ℓ) (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hnot : ¬ (-((m : ℤ) + p₂ - p₁ + i + 1) ≤ μ
        ∧ μ ≤ (M : ℤ) + m - ((m : ℤ) + p₂ - p₁ + i + 1)) := hμnot
    rcases lt_or_ge μ (-((m : ℤ) + p₂ - p₁ + i + 1)) with hlo | hge
    · rw [show ((μ : ℤ) + ((m : ℤ) + p₂ - p₁ + i + 1)) = μ + m + p₂ - p₁ + i + 1 by ring,
          cbz_apply_neg _ (by omega)]
    · have hub : (M : ℤ) + m - ((m : ℤ) + p₂ - p₁ + i + 1) < μ := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((μ : ℤ) + ((m : ℤ) + p₂ - p₁ + i + 1)) = μ + m + p₂ - p₁ + i + 1 by ring,
          cbz_lt (by positivity) (by omega)]

/-- The circle product `∘^{p₂}_m`, on the common mode range: `∑_μ C(M+m, μ+p₂+m+2) • u₍μ₎v`. -/
private theorem circ_piece27 (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmCirc W p₂ m u v
      = ∑ μ ∈ Finset.Icc (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁),
          cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + p₂ + m + 2) • W.smul u μ v := by
  rw [anmCirc, resHom_homogeneous W (m : ℤ) ((p₂ : ℤ) + (m : ℤ) + 2) hu v]
  rw [reindexToIcc27 (((M : ℤ) + (m : ℤ)).toNat) ((p₂ : ℤ) + m + 2)
      (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁)
      (fun ℓ => cbz ((M : ℤ) + (m : ℤ)) ℓ) (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hge : -((m : ℤ) + p₂ + 2) ≤ μ := hμ.1
    have hub : (M : ℤ) + m - ((p₂ : ℤ) + m + 2) < μ := by
      by_contra h; exact hμnot ⟨by omega, by omega⟩
    rw [show ((μ : ℤ) + ((p₂ : ℤ) + m + 2)) = μ + p₂ + m + 2 by ring,
        cbz_lt (by positivity) (by omega)]

/-! ## The homogeneous expansion of the off-diagonal product `∗^{p₂}_{m,p₁}`. -/

/-- `anmGen W p₂ m p₁ u v` written as a double sum over `i ∈ range(p₁+1)` (weight
`(-1)^i C(m+p₂−p₁+i, i)`, pole `m+p₂−p₁+i+1`), on homogeneous `u ∈ 𝒱_K`. -/
private theorem anmGen_offdiag_homogeneous (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ : ℕ) {K : ℤ}
    {u : 𝒱} (hu : u ∈ W.grading K) (v : 𝒱) :
    anmGen W p₂ m p₁ u v
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ ℓ ∈ Finset.range ((K + (m : ℤ)).toNat + 1),
              cbz (K + (m : ℤ)) ℓ
                • W.smul u ((ℓ : ℤ) - ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1)) v := by
  rw [anmGen]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [resHom_homogeneous W (m : ℤ) ((m : ℤ) + (p₂ : ℤ) - (p₁ : ℤ) + (i : ℤ) + 1) hu v]

/-! ## The off-diagonal absorption identity (DJ 2.7 step a), vector form. -/

private theorem anmGen_add_left' (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u₁ u₂ v : 𝒱) :
    anmGen W n m p (u₁ + u₂) v = anmGen W n m p u₁ v + anmGen W n m p u₂ v :=
  anmGen_add_left W n m p u₁ u₂ v

/-- **DJ Lemma 2.7 absorption (homogeneous).**  For homogeneous `u ∈ 𝒱_M`, the shifted grading
generator absorbed by the off-diagonal product collapses to a scalar multiple of the circle
generator:
`(L(−1)u + L(0)u + (p₁−p₂)u) ∗^{p₂}_{m,p₁} v = (−1)^{p₁} C(m+p₂, p₁) (m+p₂+1) • (u ∘^{p₂}_m v)`.
This is the residue computation of DJ Lemma 2.7 (lines 643–686); mirrors `anmGenBar_Lgen_eq`. -/
theorem anmGen_offdiag_Lgen_eq (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmGen W p₂ m p₁ (W.L (-1) u + W.L 0 u + ((p₁ : ℂ) - (p₂ : ℂ)) • u) v
      = (((-1 : ℂ) ^ p₁ * cbz ((m : ℤ) + (p₂ : ℤ)) (p₁ : ℤ)) * ((m : ℂ) + p₂ + 1))
          • anmCirc W p₂ m u v := by
  set I := Finset.Icc (-((m : ℤ) + p₂ + 2)) ((M : ℤ) + p₁) with hI
  have hLmem : W.L (-1) u ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W hu
  -- the `(L₋₁u)` summand, fully reduced to the Icc-mode form.
  have hLfull : anmGen W p₂ m p₁ (W.L (-1) u) v
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ μ ∈ I, (-((μ : ℤ) + 1)
                * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 2))
              • W.smul u μ v := by
    rw [anmGen_offdiag_homogeneous W m p₁ p₂ hLmem v]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (((M : ℤ) + 1) + (m : ℤ)) = (M : ℤ) + 1 + (m : ℤ) from by ring]
    rw [Lneg_piece27 W m p₁ p₂ M hu v i (by simpa using Finset.mem_range.mp hi)]
  -- the `u` summand, fully reduced.
  have hUfull : anmGen W p₂ m p₁ u v
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ μ ∈ I, cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1)
              • W.smul u μ v := by
    rw [anmGen_offdiag_homogeneous W m p₁ p₂ hu v]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [u_piece27 W m p₁ p₂ M hu v i (by simpa using Finset.mem_range.mp hi)]
  -- `L₀u = M•u`; split the product into the three summands and substitute.
  rw [anmGen_add_left', anmGen_add_left', L_zero_grading W u hu, anmGen_smul_left,
      anmGen_smul_left, show (((M : ℤ) : ℂ)) = (M : ℂ) from by push_cast; ring, hLfull, hUfull]
  rw [circ_piece27 W m p₁ p₂ M hu v]
  -- swap scaffold `∑_i s_i • ∑_μ c_i(μ) • T μ = ∑_μ (∑_i s_i · c_i(μ)) • T μ`.
  have swap : ∀ (c : ℕ → ℤ → ℂ),
      ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ μ ∈ I, c i μ • W.smul u μ v
        = ∑ μ ∈ I, (∑ i ∈ Finset.range (p₁ + 1),
            ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) * c i μ) • W.smul u μ v := by
    intro c
    rw [Finset.sum_congr rfl (fun i _ => by
          rw [Finset.smul_sum, Finset.sum_congr rfl (fun μ _ => by rw [smul_smul])])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_smul]
  rw [swap (fun i μ => -((μ : ℤ) + 1)
      * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 2))]
  -- distribute the `M`-factor from `L₀u` over the `u`-summand.
  have hM : (M : ℂ) • ∑ i ∈ Finset.range (p₁ + 1),
        ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
          ∑ μ ∈ I, cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1) • W.smul u μ v
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ μ ∈ I, ((M : ℂ) * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1))
              • W.smul u μ v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun μ _ => ?_)
    rw [smul_smul]
  -- distribute the `(p₁−p₂)`-factor over the `u`-summand.
  have hP : ((p₁ : ℂ) - (p₂ : ℂ)) • ∑ i ∈ Finset.range (p₁ + 1),
        ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
          ∑ μ ∈ I, cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1) • W.smul u μ v
      = ∑ i ∈ Finset.range (p₁ + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + p₂ - p₁ + i) i) •
            ∑ μ ∈ I, (((p₁ : ℂ) - (p₂ : ℂ))
                * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1))
              • W.smul u μ v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun μ _ => ?_)
    rw [smul_smul]
  rw [hM, hP, swap (fun i μ => (M : ℂ) * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1)),
      swap (fun i μ => ((p₁ : ℂ) - (p₂ : ℂ))
        * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + p₂ - p₁ + i + 1))]
  rw [Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  rw [show ((μ : ℤ) + p₂ + m + 2) = μ + m + p₂ + 2 from by ring]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← dj27_abs_scalar M m p₁ p₂ μ]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **DJ Lemma 2.7 absorption helper — the requested repo signature** (homogeneous `u`).
`(L(−1)u + L(0)u + (p₁−p₂)u) ∗^{p₂}_{m,p₁} v
  = (−1)^{p₁}·C(m+p₂, p₁)·(m+p₂+1) • (u ∘^{p₂}_m v)`,
with `u ∘^{p₂}_m v = resHom W m (m+p₂+2) u v` (`anmCirc W p₂ m`). -/
theorem anmLgen_shift_absorb (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ : ℕ) {Mu : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (Mu : ℤ)) (v : 𝒱) :
    anmGen W p₂ m p₁ (W.L (-1) u + W.L 0 u + ((p₁ : ℂ) - (p₂ : ℂ)) • u) v
      = (((-1 : ℂ) ^ p₁ * cbz ((m : ℤ) + (p₂ : ℤ)) (p₁ : ℤ)) * ((m : ℂ) + p₂ + 1))
          • resHom W (m : ℤ) ((m : ℤ) + (p₂ : ℤ) + 2) u v := by
  have h := anmGen_offdiag_Lgen_eq W m p₁ p₂ Mu hu v
  rwa [anmCirc, show ((p₂ : ℤ) + (m : ℤ) + 2) = (m : ℤ) + (p₂ : ℤ) + 2 from by ring] at h

/-! ## The vacuum is the left unit of the diagonal product `∗̄ⁿ_m = ∗ⁿ_{m,n}`.

This is what lets us instantiate `u = 𝟙` in DJ's `O''_{n,m}` generator (DJ Lemma 2.8 proof,
"With u = 1 in the definition of O''…"): the outer product `∗ⁿ_{m,n}` against the vacuum is the
identity, so the bare associator
`(a ∗ⁿ_{p₁,p₂} b) ∗ⁿ_{m,p₁} c − a ∗ⁿ_{m,p₂} (b ∗^{p₂}_{m,p₁} c)` is an `O''_{n,m}` generator. -/

/-- `resHom W m P 𝟙 x = C(m, P−1) • x`: the vacuum residue picks the single mode `ℓ = P−1`
(`W.smul 𝟙 (ℓ−P) x = x` iff `ℓ−P = −1`). -/
private theorem resHom_vacuum (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (P : ℤ) (x : 𝒱) :
    resHom W (m : ℤ) P W.vacuum x = cbz (m : ℤ) (P - 1) • x := by
  rw [resHom_homogeneous W (m : ℤ) P (vacuum_mem_grading_zero W) x, zero_add]
  -- each term: cbz(m, ℓ) • (𝟙₍ℓ−P₎ x); 𝟙₍ℓ−P₎x = x iff ℓ−P = −1, i.e. ℓ = P−1.
  have hterm : ∀ ℓ ∈ Finset.range ((m : ℤ).toNat + 1),
      cbz (m : ℤ) (ℓ : ℤ) • W.smul W.vacuum ((ℓ : ℤ) - P) x
        = (if (ℓ : ℤ) - P = -1 then cbz (m : ℤ) (ℓ : ℤ) • x else 0) := by
    intro ℓ _
    rw [show W.smul W.vacuum ((ℓ : ℤ) - P) x
          = PreVertexAlgebra.smul W.toPreVertexAlgebra W.vacuum ((ℓ : ℤ) - P) x from rfl,
        PreVertexAlgebra.smul_vacuum_left]
    split_ifs with h1
    · rfl
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm]
  -- the surviving index is ℓ with ℓ - P = -1, i.e. ℓ = P - 1.
  rcases le_or_gt 0 (P - 1) with hPnn | hPneg
  · rcases le_or_gt (P - 1) (m : ℤ) with hPle | hPgt
    · -- P-1 ∈ [0,m]: the single term at ℓ = (P-1).toNat survives.
      rw [Finset.sum_eq_single (P - 1).toNat]
      · rw [show (((P - 1).toNat : ℤ)) = P - 1 from Int.toNat_of_nonneg hPnn,
            if_pos (by ring)]
      · intro ℓ _ hℓ
        rw [if_neg]
        intro hc
        exact hℓ (by omega)
      · intro hmem
        exact absurd (by simp only [Finset.mem_range]; omega) hmem
    · -- P-1 > m: cbz(m, P-1) = 0 and no term survives.
      rw [cbz_lt (by positivity) (by omega), zero_smul]
      refine Finset.sum_eq_zero fun ℓ hℓ => ?_
      simp only [Finset.mem_range] at hℓ
      rw [if_neg (by omega)]
  · rw [cbz_apply_neg (m : ℤ) hPneg, zero_smul]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    rw [if_neg (by omega)]

/-- **The vacuum is the left unit of `∗ⁿ_{m,n} = ∗̄ⁿ_m`.**  `𝟙 ∗̄ⁿ_m x = x`.  (Off the diagonal the
vacuum annihilates; the unit holds exactly at `p = n`, which is what DJ's `u = 1` step uses.) -/
theorem anmGen_vacuum_diag (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (x : 𝒱) :
    anmGen W n m n W.vacuum x = x := by
  rw [show anmGen W n m n W.vacuum x = anmGenBar W n m W.vacuum x from rfl, anmGenBar_eq]
  -- ∑_{i∈range(n+1)} (-1)^i C(m+i,i) • resHom W m (m+i+1) 𝟙 x;  resHom = C(m, m+i) • x.
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) (i : ℤ))
          • resHom W (m : ℤ) ((m : ℤ) + (i : ℤ) + 1) W.vacuum x
        = (if i = 0 then x else 0) := by
    intro i _
    rw [resHom_vacuum W m ((m : ℤ) + (i : ℤ) + 1) x,
        show ((m : ℤ) + (i : ℤ) + 1 - 1) = (m : ℤ) + (i : ℤ) from by ring]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simp only [Nat.cast_zero, pow_zero, add_zero, cbz_zero, mul_one, one_smul, if_true]
      rw [cbz_natCast_eq_choose (le_refl m), Nat.choose_self, Nat.cast_one, one_smul]
    · -- i ≥ 1: C(m, m+i) = 0 (top m, index m+i > m).
      rw [if_neg (by omega),
          show cbz (m : ℤ) ((m : ℤ) + (i : ℤ)) = 0 from cbz_lt (by positivity) (by omega),
          zero_smul, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun _ => x),
      if_pos (by simp only [Finset.mem_range]; omega)]

/-- **The bare associator is an `O''_{n,m}` generator** (DJ Lemma 2.8 "u = 1" step).
`(a ∗ⁿ_{p₁,p₂} b) ∗ⁿ_{m,p₁} c − a ∗ⁿ_{m,p₂} (b ∗^{p₂}_{m,p₁} c) ∈ O_{n,m}(𝒱)`, obtained by setting
`u = 𝟙` in `assocDefect` (since `𝟙 ∗ⁿ_{m,n} (·) = id`). -/
theorem bareAssoc_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a b c : 𝒱) :
    anmGen W n m p₁ (anmGen W n p₁ p₂ a b) c - anmGen W n m p₂ a (anmGen W p₂ m p₁ b c)
      ∈ OnmFull W n m := by
  have h := assocDefect_mem_OnmFull W n m p₁ p₂ n a b c W.vacuum
  rwa [assocDefect, anmGen_vacuum_diag W n m _] at h

/-! ## The DJ 2.7 chain: reduce the headline to the post-reassociation cross term.

DJ's first chain step (`bareAssoc_mem_OnmFull`) reassociates
`(a ∗ⁿ_{p₁,p₂} g) ∗ⁿ_{m,p₁} v ≡ a ∗ⁿ_{m,p₂} (g ∗^{p₂}_{m,p₁} v)  (mod O_{n,m})`.
So the headline holds as soon as the **cross term** `a ∗ⁿ_{m,p₂} (g ∗^{p₂}_{m,p₁} v)` lies in `O_{n,m}`
for every `g ∈ O'_{p₂,p₁}` — which is exactly the remaining DJ chain (lines 700–712). -/

/-- **DJ Lemma 2.7 headline, reduced to the post-reassociation cross term.**
`(a ∗ⁿ_{p₁,p₂} g) ∗ⁿ_{m,p₁} v ∈ O_{n,m}(𝒱)` for `g ∈ O'_{p₂,p₁}`, **modulo** the cross-term hypothesis
`hcross : a ∗ⁿ_{m,p₂} (g ∗^{p₂}_{m,p₁} v) ∈ O_{n,m}` (DJ's chain after the first reassociation).
Proof: `bareAssoc_mem_OnmFull` gives the associator defect ∈ `O_{n,m}`; add `hcross`. -/
theorem levelMixGen_mem_OnmFull_of_cross (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ)
    (a v g : 𝒱)
    (hcross : anmGen W n m p₂ a (anmGen W p₂ m p₁ g v) ∈ OnmFull W n m) :
    anmGen W n m p₁ (anmGen W n p₁ p₂ a g) v ∈ OnmFull W n m := by
  have hassoc := bareAssoc_mem_OnmFull W n m p₁ p₂ a g v
  -- `F − G ∈ OnmFull` and `G ∈ OnmFull` ⟹ `F = (F − G) + G ∈ OnmFull`.
  have := (OnmFull W n m).add_mem hassoc hcross
  rwa [sub_add_cancel] at this

/-! ## The cross term, reduced to the two `O'_{p₂,p₁}` generator families (`span_le`). -/

/-- The cross-term action `w ↦ a ∗ⁿ_{m,p₂} (w ∗^{p₂}_{m,p₁} v)` as a ℂ-linear map in `w`
(composition of two `anmGen`-slot linear maps). -/
noncomputable def crossMap (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun w := anmGen W n m p₂ a (anmGen W p₂ m p₁ w v)
  map_add' w₁ w₂ := by
    simp only [anmGen_add_left, anmGen_add_right]
  map_smul' c w := by
    simp only [anmGen_smul_left, anmGen_smul_right, RingHom.id_apply]

@[simp] theorem crossMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v w : 𝒱) :
    crossMap W n m p₁ p₂ a v w = anmGen W n m p₂ a (anmGen W p₂ m p₁ w v) := rfl

/-- **The cross term, fed on the two `O'_{p₂,p₁}` generator families.**  If `a ∗ⁿ_{m,p₂}` of the
`∗^{p₂}_{m,p₁}`-image of each circle generator `c ∘^{p₂}_{p₁} d` and each shifted grading generator
`anmLgen W p₂ p₁ c` lies in `O_{n,m}`, then it does for every `g ∈ O'_{p₂,p₁}` (`comap`/`span_le`,
since `crossMap` is ℂ-linear).  This is the DJ chain reduced to its generator families. -/
theorem cross_mem_of_gens (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v : 𝒱)
    (hcirc : ∀ c d : 𝒱,
      anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) ∈ OnmFull W n m)
    (hL : ∀ c : 𝒱,
      anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmLgen W p₂ p₁ c) v) ∈ OnmFull W n m) :
    ∀ g ∈ Onm W p₂ p₁, anmGen W n m p₂ a (anmGen W p₂ m p₁ g v) ∈ OnmFull W n m := by
  intro g hg
  have hle : Onm W p₂ p₁ ≤ (OnmFull W n m).comap (crossMap W n m p₁ p₂ a v) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, crossMap_apply] using hcirc c d
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, crossMap_apply] using hL c
  have hx : g ∈ (OnmFull W n m).comap (crossMap W n m p₁ p₂ a v) := hle hg
  rwa [Submodule.mem_comap, crossMap_apply] at hx

/-! ## The non-homogeneous off-diagonal absorption (decompose `c` into homogeneous pieces).

The absorption scalar `(−1)^{p₁} C(m+p₂, p₁) (m+p₂+1)` is independent of the grade `M`, so the
homogeneous identity `anmGen_offdiag_Lgen_eq` lifts to arbitrary `c` by `⊕`-decomposition. -/

private theorem anmGen_offdiag_sum_left (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → 𝒱) (b : 𝒱) :
    anmGen W n m p (∑ k ∈ s, f k) b = ∑ k ∈ s, anmGen W n m p (f k) b := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : anmGen W n m p ((0 : ℂ) • (0 : 𝒱)) b = (0 : ℂ) • anmGen W n m p (0 : 𝒱) b :=
      anmGen_smul_left W n m p 0 0 b
    simpa using h0
  | insert k t hkt ih =>
    rw [Finset.sum_insert hkt, Finset.sum_insert hkt, anmGen_add_left, ih]

/-- **The off-diagonal absorption, general `c`.**  For arbitrary `c`,
`(L(−1)c + L(0)c + (p₁−p₂)c) ∗^{p₂}_{m,p₁} v = (−1)^{p₁} C(m+p₂, p₁) (m+p₂+1) • (c ∘^{p₂}_m v)`.
Decompose `c = ∑_k c_k` and apply `anmGen_offdiag_Lgen_eq` per grade (the scalar is grade-free). -/
theorem anmGen_offdiag_Lgen_eq_general (W : VertexOperatorAlgebra 𝒱) (m p₁ p₂ : ℕ) (c v : 𝒱) :
    anmGen W p₂ m p₁ (W.L (-1) c + W.L 0 c + ((p₁ : ℂ) - (p₂ : ℂ)) • c) v
      = (((-1 : ℂ) ^ p₁ * cbz ((m : ℤ) + (p₂ : ℤ)) (p₁ : ℤ)) * ((m : ℂ) + p₂ + 1))
          • anmCirc W p₂ m c v := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  set s := (DirectSum.decompose W.grading c).support with hs
  have hdecomp : ∑ k ∈ s, ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  -- rewrite the shifted generator and the circle target as sums over homogeneous pieces.
  have hgen : W.L (-1) c + W.L 0 c + ((p₁ : ℂ) - (p₂ : ℂ)) • c
      = ∑ k ∈ s, (W.L (-1) ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + W.L 0 ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + ((p₁ : ℂ) - (p₂ : ℂ))
              • ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← map_sum, ← map_sum, ← Finset.smul_sum]
    simp only [hdecomp]
  have hcirc : anmCirc W p₂ m c v
      = ∑ k ∈ s, anmCirc W p₂ m ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) v := by
    conv_lhs => rw [← hdecomp]
    rw [anmCirc]
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty]; rw [show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp,
        resHom_smul_left, zero_smul]; simp [anmCirc]
    | insert k t hkt ih =>
      rw [Finset.sum_insert hkt, Finset.sum_insert hkt, resHom_add_left, ih, anmCirc]
  rw [hgen, anmGen_offdiag_sum_left, hcirc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    rw [anmGen_offdiag_Lgen_eq W m p₁ p₂ M hk v]
  · -- k < 0: the grade is `⊥`, the piece is `0`, both sides vanish.
    have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, map_zero, map_zero, smul_zero, add_zero, add_zero,
        show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp, anmGen_smul_left, anmCirc_smul_left]
    simp

/-! ## DJ Lemma 2.7 — the headline, reduced to the DJ-chain tail (lines 705–712).

After the first reassociation (`bareAssoc`, step 1) and the `span_le` split, both `O'_{p₂,p₁}`
generator families land on the **level-`p₂` cross terms** `a ∗ⁿ_{m,p₂} (level-p₂ ideal element)`:

* **shifted grading generator** (DJ "first show" step, lines 643–686): by the off-diagonal
  absorption `anmGen_offdiag_Lgen_eq_general`, `(anmLgen W p₂ p₁ c) ∗^{p₂}_{m,p₁} v` is a scalar
  multiple of the circle generator `c ∘^{p₂}_m v`, so this family reduces to
  `a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v) ∈ O_{n,m}` — discharged here down to that exact term.
* **circle generator**: `(c ∘^{p₂}_{p₁} d) ∗^{p₂}_{m,p₁} v` is the genuine remaining content
  (DJ Lemma 2.5 sub-decomposition, lines 705–710), left as the precise residual.

We record the discharged grading-generator reduction (`hL`) and assemble the headline from the two
residuals via `cross_mem_of_gens` + `levelMixGen_mem_OnmFull_of_cross`. -/

/-- **The grading-generator family of the cross term, reduced to the level-`p₂` circle cross term.**
`a ∗ⁿ_{m,p₂} ((anmLgen W p₂ p₁ c) ∗^{p₂}_{m,p₁} v) = s • (a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v))`, so it lies in
`O_{n,m}` as soon as `a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v)` does (DJ 2.7, the "first show" step, discharged via
`anmGen_offdiag_Lgen_eq_general`). -/
theorem crossL_eq_scalar_circ (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v c : 𝒱) :
    anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmLgen W p₂ p₁ c) v)
      = (((-1 : ℂ) ^ p₁ * cbz ((m : ℤ) + (p₂ : ℤ)) (p₁ : ℤ)) * ((m : ℂ) + p₂ + 1))
          • anmGen W n m p₂ a (anmCirc W p₂ m c v) := by
  rw [show anmLgen W p₂ p₁ c
        = W.L (-1) c + W.L 0 c + ((p₁ : ℂ) - (p₂ : ℂ)) • c from rfl,
      anmGen_offdiag_Lgen_eq_general W m p₁ p₂ c v, anmGen_smul_right]

/-! ## The level-`p₂` circle cross term `a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v) ∈ O_{n,m}` (closed).

DJ Lemma 2.2 turns the circle `c ∘^{p₂}_m v` (homogeneous `c`) into a nonzero scalar multiple of
`(L(−1)c + L(0)c) ∗^{p₂}_{m,p₂} v` (the bar product against the level-`p₂` grading generator
`L(−1)c+L(0)c = anmLgen W p₂ p₂ c ∈ O_{p₂}`).  One more reassociation (`bareAssoc`) turns
`a ∗ⁿ_{m,p₂}((anmLgen W p₂ p₂ c) ∗^{p₂}_{m,p₂} v)` into the `O'''_{n,m}` generator
`(a ∗ⁿ_{p₂} (anmLgen W p₂ p₂ c)) ∗ⁿ_{m,p₂} v = levelMix …`, which is a member by
`levelMix_mem_OnmFull`.  So this residual is fully discharged. -/

/-- The DJ 2.2 scalar `(p₂+m+1)·(−1)^{p₂}·C(p₂+m, m)` is nonzero. -/
private theorem dj22_scalar_ne_zero (m p₂ : ℕ) :
    ((p₂ : ℂ) + (m : ℂ) + 1) * ((-1 : ℂ)) ^ p₂ * cbz ((p₂ : ℤ) + (m : ℤ)) (m : ℤ) ≠ 0 := by
  have hcbz : cbz ((p₂ : ℤ) + (m : ℤ)) (m : ℤ) = ((p₂ + m).choose m : ℂ) := by
    rw [show ((p₂ : ℤ) + (m : ℤ)) = (((p₂ + m : ℕ)) : ℤ) from by push_cast; ring,
        cbz_natCast_eq_choose (by omega)]
  rw [hcbz]
  have h1 : ((p₂ : ℂ) + (m : ℂ) + 1) ≠ 0 := by
    have h : ((p₂ + m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (p₂ + m)
    push_cast at h
    convert h using 1
  have h2 : ((-1 : ℂ)) ^ p₂ ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (((p₂ + m).choose m : ℕ) : ℂ) ≠ 0 := by
    have : (p₂ + m).choose m ≠ 0 := Nat.choose_pos (by omega) |>.ne'
    exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- **The level-`p₂` circle cross term, homogeneous.**  For homogeneous `c ∈ 𝒱_M`,
`a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v) ∈ O_{n,m}(𝒱)`.  Via DJ 2.2 (`anmCirc_mem_OnBar`, scalar `≠ 0`), one more
reassociation (`bareAssoc`), and the `O'''` generator `levelMix_mem_OnmFull`. -/
theorem circCross_homog_mem (W : VertexOperatorAlgebra 𝒱) (n m p₂ : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (a v : 𝒱) :
    anmGen W n m p₂ a (anmCirc W p₂ m c v) ∈ OnmFull W n m := by
  set s₂ : ℂ := ((p₂ : ℂ) + (m : ℂ) + 1) * ((-1 : ℂ)) ^ p₂ * cbz ((p₂ : ℤ) + (m : ℤ)) (m : ℤ)
    with hs₂
  have hs₂ne : s₂ ≠ 0 := dj22_scalar_ne_zero m p₂
  -- DJ 2.2: s₂ • anmCirc W p₂ m c v = anmGenBar W p₂ m (L₋₁c+L₀c) v.
  have hbar := anmCirc_mem_OnBar W p₂ m hc v
  -- so anmCirc W p₂ m c v = s₂⁻¹ • anmGenBar W p₂ m (anmLgen W p₂ p₂ c) v.
  have hcirc : anmCirc W p₂ m c v
      = s₂⁻¹ • anmGen W p₂ m p₂ (anmLgen W p₂ p₂ c) v := by
    have : anmGenBar W p₂ m (W.L (-1) c + W.L 0 c) v
        = anmGen W p₂ m p₂ (anmLgen W p₂ p₂ c) v := by
      rw [anmGenBar, anmLgen, show ((p₂ : ℂ) - (p₂ : ℂ)) = 0 from by ring, zero_smul, add_zero]
    rw [this] at hbar
    rw [← hbar, smul_smul, inv_mul_cancel₀ hs₂ne, one_smul]
  rw [hcirc, anmGen_smul_right]
  -- bareAssoc W n m p₂ p₂ a (anmLgen W p₂ p₂ c) v reassociates to the levelMix generator.
  have hassoc := bareAssoc_mem_OnmFull W n m p₂ p₂ a (anmLgen W p₂ p₂ c) v
  -- `levelMix W n m p₂ a (anmLgen W p₂ p₂ c) v ∈ OnmFull`.
  have hlevel : anmGen W n m p₂ (anmGen W n p₂ p₂ a (anmLgen W p₂ p₂ c)) v ∈ OnmFull W n m :=
    levelMix_mem_OnmFull W n m p₂ a v (anmLgen W p₂ p₂ c) (anmLgen_mem_Onm W p₂ p₂ c)
  -- the bare associator: levelMix − (a ∗ⁿ_{m,p₂}(anmLgen ∗ v)) ∈ OnmFull, and levelMix ∈ OnmFull
  --   ⟹ a ∗ⁿ_{m,p₂}(anmLgen ∗ v) ∈ OnmFull.
  have hmem : anmGen W n m p₂ a (anmGen W p₂ m p₂ (anmLgen W p₂ p₂ c) v) ∈ OnmFull W n m := by
    have := (OnmFull W n m).sub_mem hlevel hassoc
    rwa [sub_sub_cancel] at this
  exact Submodule.smul_mem _ _ hmem

/-- The level-`p₂` circle cross-term action `c ↦ a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v)` as a ℂ-linear map in
`c` (composition of `anmCirc`-left and `anmGen`-right slot maps). -/
noncomputable def circCrossMap (W : VertexOperatorAlgebra 𝒱) (n m p₂ : ℕ) (a v : 𝒱) :
    𝒱 →ₗ[ℂ] 𝒱 where
  toFun c := anmGen W n m p₂ a (anmCirc W p₂ m c v)
  map_add' c₁ c₂ := by simp only [anmCirc_add_left, anmGen_add_right]
  map_smul' r c := by simp only [anmCirc_smul_left, anmGen_smul_right, RingHom.id_apply]

@[simp] theorem circCrossMap_apply (W : VertexOperatorAlgebra 𝒱) (n m p₂ : ℕ) (a v c : 𝒱) :
    circCrossMap W n m p₂ a v c = anmGen W n m p₂ a (anmCirc W p₂ m c v) := rfl

/-- **The level-`p₂` circle cross term, general `c`.**  `a ∗ⁿ_{m,p₂} (c ∘^{p₂}_m v) ∈ O_{n,m}(𝒱)`
for arbitrary `c` (decompose `c` into homogeneous pieces, apply `circCross_homog_mem`). -/
theorem circCross_mem (W : VertexOperatorAlgebra 𝒱) (n m p₂ : ℕ) (a v c : 𝒱) :
    anmGen W n m p₂ a (anmCirc W p₂ m c v) ∈ OnmFull W n m := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading c).support,
      ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsum : anmGen W n m p₂ a (anmCirc W p₂ m c v)
      = ∑ k ∈ (DirectSum.decompose W.grading c).support,
          anmGen W n m p₂ a
            (anmCirc W p₂ m ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) v) := by
    conv_lhs => rw [← hdecomp]
    rw [← circCrossMap_apply, map_sum]
    rfl
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact circCross_homog_mem W n m p₂ hk a v
  · have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by rw [zero_smul], anmCirc_smul_left,
        anmGen_smul_right, zero_smul]
    exact (OnmFull W n m).zero_mem

/-- **The genuine residual of DJ Lemma 2.7** (the chain tail, DJ lines 705–712), reduced to its
**single** remaining piece: the off-diagonal circle cross term (the circle-generator family).  The
level-`p₂` circle cross term (the grading-generator family, post-absorption) is fully discharged by
`circCross_mem`.  The remaining `offCirc` rests on the DJ Lemma 2.5 sub-decomposition
`O'_{p₂,p₁} ∗^{p₂}_{m,p₁} V ⊆ (O_{p₂} ∗ V) ∗ V + O_{p₂} ∗ V`, not yet in the repo. -/
structure DJ27ChainTail (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ) (a v : 𝒱) : Prop where
  /-- The off-diagonal circle cross term (the circle-generator family). -/
  offCirc : ∀ c d : 𝒱,
    anmGen W n m p₂ a (anmGen W p₂ m p₁ (anmCirc W p₂ p₁ c d) v) ∈ OnmFull W n m

/-- **DJ Lemma 2.7 — the headline, modulo the DJ chain tail.**
`(a ∗ⁿ_{p₁,p₂} g) ∗ⁿ_{m,p₁} v ∈ O_{n,m}(𝒱)` for `g ∈ O'_{p₂,p₁}`, assuming the `DJ27ChainTail`
residual.  Everything else is discharged here: the first reassociation
(`bareAssoc_mem_OnmFull`, via the `u = 𝟙` vacuum-unit `anmGen_vacuum_diag`), the `span_le` split into
the two `O'_{p₂,p₁}` generator families (`cross_mem_of_gens`), and the off-diagonal absorption of the
shifted grading generator (`crossL_eq_scalar_circ`, via `anmGen_offdiag_Lgen_eq_general`). -/
theorem levelMixGen_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m p₁ p₂ : ℕ)
    (a v : 𝒱) (g : 𝒱) (hg : g ∈ Onm W p₂ p₁)
    (htail : DJ27ChainTail W n m p₁ p₂ a v) :
    anmGen W n m p₁ (anmGen W n p₁ p₂ a g) v ∈ OnmFull W n m := by
  -- step 1: reduce to the cross term `a ∗ⁿ_{m,p₂} (g ∗^{p₂}_{m,p₁} v)`.
  refine levelMixGen_mem_OnmFull_of_cross W n m p₁ p₂ a v g ?_
  -- step 2: `span_le` over the two `O'_{p₂,p₁}` generators.
  refine cross_mem_of_gens W n m p₁ p₂ a v ?_ ?_ g hg
  · -- circle generator family = the `offCirc` residual.
    exact htail.offCirc
  · -- shifted grading generator family: absorb to the circle cross term, then `circCross_mem`.
    intro c
    rw [crossL_eq_scalar_circ W n m p₁ p₂ a v c]
    exact Submodule.smul_mem _ _ (circCross_mem W n m p₂ a v c)

end VOA