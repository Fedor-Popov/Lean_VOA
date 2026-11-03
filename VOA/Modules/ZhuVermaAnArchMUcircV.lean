/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcircClose

/-!
# Game One — closing the **V-core**, hence `AnmCircTowerEq ⟹ hcirc ⟹ AnmRightModule`.

This file discharges the single remaining scalar core of the `m = 0` (shift-`0`, `j`-free) circle
tower decomposition `AnmCircTowerEq` — the **V-core** base-`P` tower collapse

  `VgammaModeCollAnm M P n G γ μ = -towerCoeffAnm P n (wV γ) ((n+2+γ).toNat) μ`,

mirror of `ZhuVermaAnArchL1Close.VgammaModeCollLn_eq_towerCoeff` (`GvLn` route, `ZhuVermaAnDescent20`)
but `j`-free (single residue).  Combined with the PROVEN U-core
(`ZhuVermaAnArchMUcircClose.UgammaModeCollAnm_eq_towerCoeff`) it closes the universal
`AnmCircTowerEq` for all homogeneous `c, d, v` (via `AnmCircTowerEq_of_sides`), hence `hcirc` (via
`ZhuVermaAnArchMUcirc.hcirc_of_towerEq`), hence `AnmRightModule W n` (via
`AnmRightModule_of_towerEq`).

## The V-core route (exploratory computer-algebra evidence not retained)

Starting from the PROVEN reduction `VgammaModeCollAnm = VInnerIAnm` (`VgammaModeCollAnm_eq_VInnerIAnm`),
with (for `0 ≤ γ`)
`VInnerIAnm = ∑_{i≤M} C(M,i)·C((M+P+n+1)-i, M+P-n-2-μ-γ)·((-1)^(i-(n+2))·C(γ-1-(i-(n+2)), γ))`:

* `VInnerIAnm_eq_VASumAnm` — Vandermonde top-split `(M+P+n+1)-i = (M-i)+(P+n+1)`, swap `a`-outer,
  `trinom_symm` pulls `C(M,a)` out, then the inner `i`-collapse
  `∑_i C(M-a,i)·(-1)^(i-(n+2))·C(γ-1-(i-(n+2)), γ) = (-1)^(n+2)·C((γ+n+1)-(M-a), γ-(M-a))`
  (`VICAnm_collapse`, via `SV_collapse`).
* `VASumAnm_eq_kFinsum` — reflect `a ↦ M-a`, `cbz_symm` the carrier `C(P+n+1, ·)` so its argument is
  `(μ+(n+2))+k`, giving the kernel `VHkerAnm(k) = C(M, (n+1+γ)-k)·C(k, k-(n+1))`.
* `VInnerIAnm_eq_GvAnmFinsum` — `(n+1)`-Vandermonde split `P+n+1 = (n+1)+P` to base `P`, kernel
  `GvAnm(kp) = ∑_t C(n+1,t)·VHkerAnm(kp+t)`.
* `VInnerIAnm_tower` — `tower_swap` (base `P`, support `[0,(n+2+γ).toNat)` from `GvAnm_lo`/`GvAnm_hi`).
* `VgammaModeCollAnm_eq_towerCoeff` — the V-core, with `wVAnm` carrying the retained sign
  `-(-1)^(n+2)` (and vanishing for `γ < 0`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
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

/-! ## Step 1 — the V-core inner `i`-collapse and the reduced `a`-sum `VASumAnm`. -/

/-- **The per-`a` V-inner `i`-collapse** (shift-`0`, `j`-free).  For `a ≤ M`,
`∑_i C(M-a,i)·(-1)^(i-(n+2))·C(γ-1-(i-(n+2)), γ) = (-1)^(n+2)·C((γ+n+1)-(M-a), γ-(M-a))`.

The inner factor `C(γ-1-(i-(n+2)), γ) = C((γ+n+1)-i, γ)` and the sign `(-1)^(i-(n+2)) =
(-1)^(n+2)·(-1)^i` (pull the `i`-independent `(-1)^(n+2)` out), then `SV_collapse` with `Q = M-a`,
`R = γ+n+1`, `S = γ`.  Shift-`0`, `j`-free analogue of `ZhuVermaAnDescent20.VIC_collapse`. -/
theorem VICAnm_collapse (M n a : ℕ) (γ : ℤ) (ha : a ≤ M) :
    (∑ i ∈ Finset.range (M + 1),
        cbz ((M : ℤ) - a) (i : ℤ)
          * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))
              * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ))
      = ((-1 : ℂ) ^ ((n : ℤ) + 2))
          * cbz ((γ + (n : ℤ) + 1) - ((M : ℤ) - a)) (γ - ((M : ℤ) - a)) := by
  have hca : ((M - a : ℕ) : ℤ) = (M : ℤ) - a := by rw [Nat.cast_sub ha]
  -- normalize the sign and the inner-factor top.
  rw [show (∑ i ∈ Finset.range (M + 1),
            cbz ((M : ℤ) - a) (i : ℤ)
              * ((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))
                  * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ))
        = ((-1 : ℂ) ^ ((n : ℤ) + 2))
            * ∑ i ∈ Finset.range (M + 1),
                (-1 : ℂ) ^ i * cbz ((M - a : ℕ) : ℤ) (i : ℤ)
                  * cbz ((γ + (n : ℤ) + 1) - (i : ℤ)) γ from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hca]
      -- `(-1)^(i-(n+2)) = (-1)^(n+2) · (-1)^i` (zpow over ℤ; `(-1)^(n+2)` is its own inverse).
      have hsq : ((-1 : ℂ) ^ ((n : ℤ) + 2)) * ((-1 : ℂ) ^ ((n : ℤ) + 2)) = 1 := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
          show ((n : ℤ) + 2) + ((n : ℤ) + 2) = (((2 * n + 4 : ℕ)) : ℤ) from by push_cast; ring,
          zpow_natCast, show 2 * n + 4 = 2 * (n + 2) from by ring, pow_mul]
        norm_num
      have hinv : ((-1 : ℂ) ^ ((n : ℤ) + 2))⁻¹ = (-1 : ℂ) ^ ((n : ℤ) + 2) :=
        inv_eq_of_mul_eq_one_right hsq
      have hsgn : (-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2))
          = ((-1 : ℂ) ^ ((n : ℤ) + 2)) * (-1 : ℂ) ^ i := by
        rw [show (i : ℤ) - ((n : ℤ) + 2) = (i : ℤ) + (-((n : ℤ) + 2)) from by ring,
          zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, zpow_neg, hinv]
        ring
      rw [hsgn,
        show γ - 1 - ((i : ℤ) - ((n : ℤ) + 2)) = (γ + (n : ℤ) + 1) - (i : ℤ) from by ring]
      ring]
  congr 1
  rw [SV_collapse (M - a) (γ + (n : ℤ) + 1) γ (N := M + 1) (by omega), hca]

/-- The shift-`0` V `a`-sum (Vandermonde top-split + `trinom_symm` + `VICAnm_collapse`, carrier
`P+n+1`).  `j`-free mirror of `ZhuVermaAnDescent20.VASum`. -/
noncomputable def VASumAnm (M P n : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    ((-1 : ℂ) ^ ((n : ℤ) + 2))
      * ∑ a ∈ Finset.range (M + 1),
          cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
            * cbz (M : ℤ) (a : ℤ)
            * cbz ((γ + (n : ℤ) + 1) - ((M : ℤ) - a)) (γ - ((M : ℤ) - a))
  else 0

/-- **`VInnerIAnm = VASumAnm`.**  `j`-free mirror of `ZhuVermaAnDescent20`'s `VInnerILn = VASumLn`. -/
theorem VInnerIAnm_eq_VASumAnm (M P n : ℕ) (γ μ : ℤ) :
    VInnerIAnm M P n γ μ = VASumAnm M P n γ μ := by
  rw [VInnerIAnm, VASumAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    rw [show ∑ i ∈ Finset.range (M + 1),
              cbz (M : ℤ) (i : ℤ)
                * cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
                * (((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                    * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ)
          = ∑ i ∈ Finset.range (M + 1), ∑ a ∈ Finset.range (M + 1),
              cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
                * (cbz (M : ℤ) (i : ℤ) * cbz ((M : ℤ) - (i : ℤ)) (a : ℤ)
                    * (((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                        * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ)) from
        Finset.sum_congr rfl fun i hi => ?_]
    · rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hale : a ≤ M := by have := Finset.mem_range.mp ha; omega
      rw [← Finset.mul_sum]
      -- pull `C(M,a)` out (`trinom_symm`), then `VICAnm_collapse`.
      rw [show ∑ i ∈ Finset.range (M + 1),
                cbz (M : ℤ) (i : ℤ) * cbz ((M : ℤ) - (i : ℤ)) (a : ℤ)
                  * (((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                      * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ)
            = cbz (M : ℤ) (a : ℤ)
                * ∑ i ∈ Finset.range (M + 1),
                    cbz ((M : ℤ) - a) (i : ℤ)
                      * (((-1 : ℂ) ^ ((i : ℤ) - ((n : ℤ) + 2)))
                          * cbz (γ - 1 - ((i : ℤ) - ((n : ℤ) + 2))) γ) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (M : ℤ) = ((M : ℕ) : ℤ) from rfl, trinom_symm M (i : ℤ) (a : ℤ)]
        ring]
      rw [VICAnm_collapse M n a γ hale]
      ring
    · have hile : i ≤ M := by have := Finset.mem_range.mp hi; omega
      have hmid : cbz (((M : ℤ) + P + n + 1) - i) ((M : ℤ) + P - n - 2 - μ - γ)
          = ∑ a ∈ Finset.range (M + 1),
              cbz ((M - i : ℕ) : ℤ) (a : ℤ)
                * cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a) := by
        rw [vandermonde_range_top (M - i) ((P : ℤ) + n + 1)
          ((M : ℤ) + P - n - 2 - μ - γ) (N := M + 1) (by omega)]
        congr 1
        rw [Nat.cast_sub hile]; ring
      rw [hmid, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show ((M - i : ℕ) : ℤ) = (M : ℤ) - i from by rw [Nat.cast_sub hile]]
      ring
  · rw [if_neg hγ, if_neg hγ]

/-! ## Step 1 (cont.) — the carrier kernel `VHkerAnm`, the base-`P` finsum, and the tower. -/

/-- The shift-`0` V per-`k` carrier kernel `VHkerAnm M n γ k = C(M, (n+1+γ)-k)·C(k, k-(n+1))`.
After reflecting `a ↦ M-a` and `cbz_symm`-reindexing the carrier `C(P+n+1, ·)` so its argument is
`(μ+(n+2))+k`, this is the residual `a`-factor.  `j`-free mirror of `ZhuVermaAnDescent20.VHkerLn`. -/
noncomputable def VHkerAnm (M n : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz (M : ℤ) (((n : ℤ) + 1 + γ) - k) * cbz k (k - ((n : ℤ) + 1))

/-- **`VASumAnm` as a `cbz(P+n+1, (μ+(n+2))+k)`-finsum.**  Reflect `a ↦ M-a`, then `cbz_symm` the
carrier `C(P+n+1, (P-n-2-μ-γ)+a) = C(P+n+1, (μ+(n+2))+(n+1+γ-a))`, substitute `k = n+1+γ-a`.  `j`-free
mirror of `VASumLn_eq_kFinsum`. -/
theorem VASumAnm_eq_kFinsum (M P n : ℕ) (γ μ : ℤ) :
    VASumAnm M P n γ μ
      = if 0 ≤ γ then
          ((-1 : ℂ) ^ ((n : ℤ) + 2))
            * ∑ᶠ k : ℤ, cbz ((P : ℤ) + n + 1) (((μ : ℤ) + (n + 2)) + k) * VHkerAnm M n γ k
        else 0 := by
  rw [VASumAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    congr 1
    rw [← Finset.sum_range_reflect
        (fun a => cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - a)
            * cbz (M : ℤ) (a : ℤ)
            * cbz ((γ + (n : ℤ) + 1) - ((M : ℤ) - a)) (γ - ((M : ℤ) - a))) (M + 1)]
    rw [show (∑ a ∈ Finset.range (M + 1),
              cbz ((P : ℤ) + n + 1) (((M : ℤ) + P - n - 2 - μ - γ) - ((M + 1 - 1 - a : ℕ) : ℤ))
                  * cbz (M : ℤ) ((M + 1 - 1 - a : ℕ) : ℤ)
                  * cbz ((γ + (n : ℤ) + 1) - ((M : ℤ) - ((M + 1 - 1 - a : ℕ) : ℤ)))
                      (γ - ((M : ℤ) - ((M + 1 - 1 - a : ℕ) : ℤ))))
          = ∑ a ∈ Finset.range (M + 1),
              cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                * (cbz (M : ℤ) (a : ℤ)
                    * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)) from
        Finset.sum_congr rfl fun a ha => ?_]
    · rw [show (∑ a ∈ Finset.range (M + 1),
                cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                  * (cbz (M : ℤ) (a : ℤ)
                      * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)))
            = ∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                  * (cbz (M : ℤ) a
                      * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)) from ?_]
      · -- `cbz_symm` the carrier, then reindex `k = (n+1+γ) - a`.
        rw [show (∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
                  * (cbz (M : ℤ) a
                      * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)))
              = ∑ᶠ a : ℤ, cbz ((P : ℤ) + n + 1)
                    (((μ : ℤ) + (n + 2)) + (((n : ℤ) + 1 + γ) - a))
                  * (cbz (M : ℤ) a
                      * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)) from
          finsum_congr fun a => by
            rw [show ((P : ℤ) + n + 1) = (((P + n + 1 : ℕ)) : ℤ) from by push_cast; ring,
              ZhuMu.cbz_symm (P + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)]
            congr 2
            push_cast; ring]
        rw [← finsum_comp_equiv (Equiv.subLeft ((n : ℤ) + 1 + γ))
            (f := fun a : ℤ => cbz ((P : ℤ) + n + 1)
                  (((μ : ℤ) + (n + 2)) + (((n : ℤ) + 1 + γ) - a))
                * (cbz (M : ℤ) a
                    * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)))]
        simp only [Equiv.subLeft_apply]
        refine finsum_congr fun k => ?_
        rw [VHkerAnm,
          show ((n : ℤ) + 1 + γ) - (((n : ℤ) + 1 + γ) - k) = k from by ring,
          show (γ + (n : ℤ) + 1) - (((n : ℤ) + 1 + γ) - k) = k from by ring,
          show γ - (((n : ℤ) + 1 + γ) - k) = k - ((n : ℤ) + 1) from by ring]
      · refine (finsumZ_eq_range_sum (N := M + 1)
          (fun a : ℤ => cbz ((P : ℤ) + n + 1) (((P : ℤ) - n - 2 - μ - γ) + a)
              * (cbz (M : ℤ) a
                  * cbz ((γ + (n : ℤ) + 1) - a) (γ - a)))
          (fun p hp => by dsimp only; rw [cbz_apply_neg (M : ℤ) hp, zero_mul, mul_zero])
          (fun p hp => by
            dsimp only
            rw [cbz_lt (by positivity) (by
              have : (M + 1 : ℤ) ≤ p := by exact_mod_cast hp
              omega : (M : ℤ) < p), zero_mul, mul_zero])).symm
    · have hale : a ≤ M := by have := Finset.mem_range.mp ha; omega
      rw [show M + 1 - 1 - a = M - a from by omega]
      have hca : (((M - a : ℕ) : ℤ)) = (M : ℤ) - a := by rw [Nat.cast_sub hale]
      rw [hca]
      rw [show cbz (M : ℤ) ((M : ℤ) - a) = cbz (M : ℤ) (a : ℤ) from by
          rw [show (M : ℤ) = ((M : ℕ) : ℤ) from rfl, ← ZhuMu.cbz_symm M (a : ℤ)]]
      rw [show ((M : ℤ) + P - n - 2 - μ - γ) - ((M : ℤ) - a) = ((P : ℤ) - n - 2 - μ - γ) + a from by ring,
        show (γ + (n : ℤ) + 1) - ((M : ℤ) - ((M : ℤ) - a)) = (γ + (n : ℤ) + 1) - a from by ring,
        show γ - ((M : ℤ) - ((M : ℤ) - a)) = γ - a from by ring]
      ring
  · rw [if_neg hγ, if_neg hγ]

/-- The base-`P` per-`kp` kernel: `GvAnm M n γ kp = ∑_t C(n+1,t)·VHkerAnm M n γ (kp+t)`.  `j`-free
mirror of `ZhuVermaAnDescent20.GvLn`. -/
noncomputable def GvAnm (M n : ℕ) (γ : ℤ) (kp : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (n + 1 + 1), cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ (kp + t)

/-- `VHkerAnm` vanishes below `n+1` (the `C(k, k-(n+1))` factor: lower `< 0` for `k < n+1`). -/
theorem VHkerAnm_lo (M n : ℕ) (γ : ℤ) {k : ℤ} (hk : k < (n : ℤ) + 1) : VHkerAnm M n γ k = 0 := by
  rw [VHkerAnm, cbz_apply_neg k (by omega : k - ((n : ℤ) + 1) < 0), mul_zero]

/-- `VHkerAnm` vanishes above `n+1+γ` (the `C(M, (n+1+γ)-k)` factor: lower `< 0`). -/
theorem VHkerAnm_hi (M n : ℕ) (γ : ℤ) {k : ℤ} (hk : (n : ℤ) + 1 + γ < k) : VHkerAnm M n γ k = 0 := by
  rw [VHkerAnm, cbz_apply_neg (M : ℤ) (by omega : ((n : ℤ) + 1 + γ) - k < 0), zero_mul]

/-- **`VInnerIAnm` as a base-`P` finsum** (`(n+1)`-Vandermonde `P+n+1 = (n+1)+P`).  `j`-free mirror of
`VInnerILn_eq_GvLnFinsum`. -/
theorem VInnerIAnm_eq_GvAnmFinsum (M P n : ℕ) (γ μ : ℤ) :
    VInnerIAnm M P n γ μ
      = if 0 ≤ γ then
          ((-1 : ℂ) ^ ((n : ℤ) + 2))
            * ∑ᶠ kp : ℤ, cbz (P : ℤ) (((μ : ℤ) + (n + 2)) + kp) * GvAnm M n γ kp
        else 0 := by
  rw [VInnerIAnm_eq_VASumAnm, VASumAnm_eq_kFinsum]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    congr 1
    have hsplit : ∀ k : ℤ,
        cbz ((P : ℤ) + n + 1) (((μ : ℤ) + (n + 2)) + k)
          = ∑ᶠ t : ℤ, cbz ((n : ℤ) + 1) t * cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t) := by
      intro k
      rw [show (P : ℤ) + n + 1 = ((n : ℤ) + 1) + (P : ℤ) from by ring,
        ← cbz_vandermonde ((n : ℤ) + 1) (P : ℤ) (((μ : ℤ) + (n + 2)) + k), cbzConvol]
    rw [show (∑ᶠ k : ℤ, cbz ((P : ℤ) + n + 1) (((μ : ℤ) + (n + 2)) + k) * VHkerAnm M n γ k)
          = ∑ᶠ k : ℤ, ∑ t ∈ Finset.range (n + 1 + 1),
              cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k) from
        finsum_congr fun k => by
          rw [hsplit k, finsum_mul,
            finsumZ_eq_range_sum (N := n + 1 + 1)
              (fun t : ℤ => cbz ((n : ℤ) + 1) t * cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                  * VHkerAnm M n γ k)
              (fun p hp => by dsimp only; rw [cbz_apply_neg ((n : ℤ) + 1) hp, zero_mul, zero_mul])
              (fun p hp => by
                dsimp only
                rw [cbz_lt (by positivity) (by
                  have : (n + 1 + 1 : ℤ) ≤ p := by exact_mod_cast hp
                  omega : (n : ℤ) + 1 < p), zero_mul, zero_mul])]
          refine Finset.sum_congr rfl fun t _ => by ring]
    rw [show (∑ᶠ k : ℤ, ∑ t ∈ Finset.range (n + 1 + 1),
              cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k))
          = ∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ k : ℤ,
              cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k) from by
        rw [← sum_finsum_comm (Finset.range (n + 1 + 1))
            (fun t k => cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k))
            (fun t _ => ?_)]
        apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1) ((n : ℤ) + 1 + γ))
        intro k hk
        rw [Function.mem_support] at hk
        rw [Set.mem_Icc]
        by_contra hcon
        apply hk
        simp only []
        rcases not_and_or.mp hcon with h | h
        · rw [VHkerAnm_lo M n γ (by omega : k < (n : ℤ) + 1), mul_zero, mul_zero]
        · rw [VHkerAnm_hi M n γ (by omega : (n : ℤ) + 1 + γ < k), mul_zero, mul_zero]]
    rw [show (∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ k : ℤ,
              cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k))
          = ∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ kp : ℤ,
              cbz (P : ℤ) (((μ : ℤ) + (n + 2)) + kp)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ (kp + (t : ℤ))) from
        Finset.sum_congr rfl fun t _ => by
          rw [← finsum_comp_equiv (Equiv.addRight (t : ℤ))
              (f := fun k : ℤ => cbz (P : ℤ) ((((μ : ℤ) + (n + 2)) + k) - t)
                  * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ k))]
          simp only [Equiv.coe_addRight]
          refine finsum_congr fun kp => by
            rw [show (((μ : ℤ) + (n + 2)) + (kp + (t : ℤ))) - t = ((μ : ℤ) + (n + 2)) + kp from by
              ring]]
    have hfin : ∀ t ∈ Finset.range (n + 1 + 1),
        Function.HasFiniteSupport (fun kp : ℤ => cbz (P : ℤ) (((μ : ℤ) + (n + 2)) + kp)
            * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ (kp + (t : ℤ)))) := by
      intro t _
      apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1 - t) ((n : ℤ) + 1 + γ - t))
      intro kp hkp
      rw [Function.mem_support] at hkp
      rw [Set.mem_Icc]
      by_contra hcon
      apply hkp
      rcases not_and_or.mp hcon with h | h
      · rw [VHkerAnm_lo M n γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1), mul_zero, mul_zero]
      · rw [VHkerAnm_hi M n γ (by omega : (n : ℤ) + 1 + γ < kp + (t : ℤ)), mul_zero, mul_zero]
    rw [sum_finsum_comm (Finset.range (n + 1 + 1))
        (fun t kp => cbz (P : ℤ) (((μ : ℤ) + (n + 2)) + kp)
            * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerAnm M n γ (kp + (t : ℤ)))) hfin]
    refine finsum_congr fun kp => ?_
    rw [GvAnm, Finset.mul_sum]
  · rw [if_neg hγ, if_neg hγ]

/-! ## Step 1 (cont.) — the grade-`P` tower collapse and the V-core. -/

/-- `GvAnm` vanishes for `kp < 0` (every `VHkerAnm(kp+t)` term has `kp+t < n+1`). -/
theorem GvAnm_lo (M n : ℕ) (γ : ℤ) {kp : ℤ} (hkp : kp < 0) : GvAnm M n γ kp = 0 := by
  rw [GvAnm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (t : ℤ) ≤ (n : ℤ) + 1 := by
    have := Finset.mem_range.mp ht; exact_mod_cast (by omega : t ≤ n + 1)
  rw [VHkerAnm_lo M n γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1), mul_zero]

/-- `GvAnm` vanishes for `n+2+γ ≤ kp` (every `VHkerAnm(kp+t)` term has `n+1+γ < kp+t`). -/
theorem GvAnm_hi (M n : ℕ) (γ : ℤ) {kp : ℤ} (hkp : (n : ℤ) + 2 + γ ≤ kp) : GvAnm M n γ kp = 0 := by
  rw [GvAnm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  rw [VHkerAnm_hi M n γ (by omega : (n : ℤ) + 1 + γ < kp + (t : ℤ)), mul_zero]

/-- The shift-`0` V per-tower weight (`tower_swap` weight at base `P`, support `[0, (n+2+γ).toNat)`). -/
noncomputable def vtAnm (M n : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ kp ∈ Finset.range ((n : ℤ) + 2 + γ).toNat,
    (-1 : ℂ) ^ (kp - ν) * cbz (kp : ℤ) (ν : ℤ) * GvAnm M n γ (kp : ℤ)

/-- **`VInnerIAnm` tower collapse** (grade `P`).  `j`-free mirror of `VInnerILn_tower`. -/
theorem VInnerIAnm_tower (M P n : ℕ) (γ μ : ℤ) :
    VInnerIAnm M P n γ μ
      = if 0 ≤ γ then
          ((-1 : ℂ) ^ ((n : ℤ) + 2))
            * ∑ ν ∈ Finset.range ((n : ℤ) + 2 + γ).toNat,
                vtAnm M n γ ν * cbz ((P : ℤ) + ν) ((μ + (n + 2)) + ν)
        else 0 := by
  rw [VInnerIAnm_eq_GvAnmFinsum]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    congr 1
    rw [show (∑ᶠ kp : ℤ, cbz (P : ℤ) (((μ : ℤ) + (n + 2)) + kp) * GvAnm M n γ kp)
          = ∑ᶠ kp : ℤ, cbz (((P : ℕ)) : ℤ) (((μ : ℤ) + (n + 2)) + kp) * GvAnm M n γ kp from by
        rfl]
    rw [tower_swap P (μ + (n + 2)) (GvAnm M n γ) ((n : ℤ) + 2 + γ).toNat
        (fun k hk => GvAnm_lo M n γ hk)
        (fun k hk => GvAnm_hi M n γ (by
          have hh : (((n : ℤ) + 2 + γ).toNat : ℤ) ≤ k := hk
          rcases lt_or_ge ((n : ℤ) + 2 + γ) 0 with h | h
          · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
          · rw [Int.toNat_of_nonneg h] at hh; omega))]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [vtAnm]
  · rw [if_neg hγ, if_neg hγ]

/-- **The shift-`0` V-core weights**: `wVAnm M n γ ν = -(-1)^(n+2) · vtAnm M n γ ν` for `0 ≤ γ`, else
`0`.  The retained sign `-(-1)^(n+2)` turns `(-1)^(n+2) · tower` into `-towerCoeffAnm`. -/
noncomputable def wVAnm (M n : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  if 0 ≤ γ then -((-1 : ℂ) ^ ((n : ℤ) + 2)) * vtAnm M n γ ν else 0

/-- **The V-core scalar collapse** (grade `P`).  `VgammaModeCollAnm` equals the *negated* grade-`P`
`towerCoeffAnm` tower with weights `wVAnm` and depth `Δ = (n+2+γ).toNat`.  `j`-free mirror of
`ZhuVermaAnArchL1Close.VgammaModeCollLn_eq_towerCoeff`. -/
theorem VgammaModeCollAnm_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1)
    (γ μ : ℤ) :
    VgammaModeCollAnm M P n G γ μ
      = -towerCoeffAnm P n (wVAnm M n γ) ((n : ℤ) + 2 + γ).toNat μ := by
  rw [VgammaModeCollAnm_eq_VInnerIAnm M P n G hG γ μ, VInnerIAnm_tower, towerCoeffAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [wVAnm, if_pos hγ]
    ring
  · rw [if_neg hγ]
    symm
    refine (neg_eq_zero.mpr (Finset.sum_eq_zero fun ν _ => ?_))
    rw [wVAnm, if_neg hγ, zero_mul]

/-! ## Step 2 — the side collapses and the universal `AnmCircTowerEq`, hence `AnmRightModule`.

With the U-core (`UgammaModeCollAnm_eq_towerCoeff`, PROVEN in `ZhuVermaAnArchMUcircClose`) and the
V-core just proved, the two sides collapse onto the `PresAnm`-tower families, and
`AnmCircTowerEq_of_sides` assembles the universal tower predicate.  Mirror of
`ZhuVermaAnArchL1Close` Step L-7. -/

/-- The shift-`0` grade witness `Gwit M P n i = (M+P-(i-(n+2))-1).toNat`, matching the inner circle
grade on the always-true `i ≤ M` range.  Mirror of `ZhuVermaAnDescent21.Gwit`. -/
noncomputable def GwitAnm (M P n : ℕ) (i : ℕ) : ℕ :=
  ((M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1).toNat

/-- `GwitAnm` realizes the inner grade whenever it is nonnegative. -/
theorem GwitAnm_spec (M P n : ℕ) :
    ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 →
      (GwitAnm M P n i : ℤ) = (M : ℤ) + P - ((i : ℤ) - ((n : ℤ) + 2)) - 1 := by
  intro i hi
  rw [GwitAnm, Int.toNat_of_nonneg hi]

/-- `towerCoeffAnm` is unchanged by padding a weight that vanishes past `Δ₀`.  Shift-`0` analogue of
`towerCoeff_pad`. -/
theorem towerCoeffAnm_pad (M n : ℕ) (wt : ℕ → ℂ) (Δ₀ Δ : ℕ) (μ : ℤ)
    (hle : Δ₀ ≤ Δ) (hvan : ∀ δ : ℕ, Δ₀ ≤ δ → wt δ = 0) :
    towerCoeffAnm M n wt Δ μ = towerCoeffAnm M n wt Δ₀ μ := by
  rw [towerCoeffAnm, towerCoeffAnm]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hle) ?_
  intro δ _ hδ
  rw [hvan δ (by rw [Finset.mem_range] at hδ; omega), zero_mul]

/-- `wUAnm` vanishes past depth `(n+2+γ).toNat` (the `cbz(k, ν) = 0` factor for `k < ν`). -/
theorem wUAnm_vanish (P n : ℕ) (γ : ℤ) {δ : ℕ} (hδ : ((n : ℤ) + 2 + γ).toNat ≤ δ) :
    wUAnm P n γ δ = 0 := by
  rw [wUAnm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < ((n : ℤ) + 2 + γ).toNat := Finset.mem_range.mp hk
  rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : k < δ)), mul_zero, zero_mul]

/-- `wVAnm` vanishes past depth `(n+2+γ).toNat` (the `cbz(kp, ν) = 0` factor for `kp < ν`). -/
theorem wVAnm_vanish (M n : ℕ) (γ : ℤ) {δ : ℕ} (hδ : ((n : ℤ) + 2 + γ).toNat ≤ δ) :
    wVAnm M n γ δ = 0 := by
  rw [wVAnm]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ]
    rw [show vtAnm M n γ δ = 0 from ?_, mul_zero]
    rw [vtAnm]
    refine Finset.sum_eq_zero fun kp hkp => ?_
    have hkp' : kp < ((n : ℤ) + 2 + γ).toNat := Finset.mem_range.mp hkp
    rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : kp < δ)), mul_zero, zero_mul]
  · rw [if_neg hγ]

/-- The collected U scalar `UgammaModeCollAnm` vanishes for `γ < -(n+1)` (its `UgammaCoeffAnm` guard
`(p-(n+1)) ≤ γ` fails for all `p ≥ 0`). -/
theorem UgammaModeCollAnm_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ)
    (hγ : γ < -((n : ℤ) + 1)) : UgammaModeCollAnm M P n G γ μ = 0 := by
  rw [UgammaModeCollAnm]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show UgammaCoeffAnm M P n G i p γ = 0 from by
    rw [UgammaCoeffAnm, if_neg (by
      have hp : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
      omega)], ite_self]

/-- The collected V scalar `VgammaModeCollAnm` vanishes for `γ < 0` (its `VgammaCoeffAnm` guard). -/
theorem VgammaModeCollAnm_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) (hγ : γ < 0) :
    VgammaModeCollAnm M P n G γ μ = 0 := by
  rw [VgammaModeCollAnm]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show VgammaCoeffAnm M P n G i p γ = 0 from by rw [VgammaCoeffAnm, if_neg (by omega)],
    ite_self]

/-- The U-side double-finsum body vanishes once the base `d₍γ₎v = 0`. -/
theorem USideAnm_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (G : ℕ → ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ v = 0) (γ : ℤ) (hγ : Nd ≤ γ) :
    (∑ᶠ μ : ℤ, UgammaModeCollAnm M P n G γ μ • W.smul c μ (W.smul d γ v)) = 0 := by
  rw [show W.smul d γ v = (0 : 𝒱) from hNd γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- The V-side double-finsum body vanishes once the base `c₍γ₎v = 0`. -/
theorem VSideAnm_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (G : ℕ → ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ v = 0) (γ : ℤ) (hγ : Nc ≤ γ) :
    (∑ᶠ μ : ℤ, VgammaModeCollAnm M P n G γ μ • W.smul d μ (W.smul c γ v)) = 0 := by
  rw [show W.smul c γ v = (0 : 𝒱) from hNc γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- **U-side collapse** `USideAnm = UfamAnm` over a window/depth.  `j`-free mirror of
`USideLn_eq_UfamOn`. -/
theorem USideAnm_eq_UfamAnm (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ v = 0)
    (hγ₀ : γ₀ ≤ -((n : ℤ) + 1)) (hΓ : Nd ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → ((n : ℤ) + 2 + γ).toNat ≤ Δ) :
    USideAnm W M P n c d v (GwitAnm M P n) = UfamAnm W M n c d v (wUAnm P n) γ₀ Γ Δ := by
  rw [USideAnm_eq_gammaModeFinsum, UfamAnm_eq_finsum]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, UgammaModeCollAnm M P n (GwitAnm M P n) γ μ • W.smul c μ (W.smul d γ v))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    refine finsum_congr fun μ => ?_
    congr 1
    rw [UgammaModeCollAnm_eq_towerCoeff M P n (GwitAnm M P n) (GwitAnm_spec M P n) (γ₀ + (g : ℤ)) μ]
    rw [towerCoeffAnm_pad M n (wUAnm P n (γ₀ + (g : ℤ))) ((n : ℤ) + 2 + (γ₀ + (g : ℤ))).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => wUAnm_vanish P n (γ₀ + (g : ℤ)) hδ)]
  · intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [UgammaModeCollAnm_zero_below M P n (GwitAnm M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact USideAnm_gammaBody_zero_above W M P n c d v (GwitAnm M P n) hNd γ (by omega)

/-- **V-side collapse** `VSideAnm = -VfamAnm` over a window/depth.  `j`-free mirror of
`VSideLn_eq_neg_VfamOn`. -/
theorem VSideAnm_eq_neg_VfamAnm (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d v : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ v = 0)
    (hγ₀ : γ₀ ≤ 0) (hΓ : Nc ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → ((n : ℤ) + 2 + γ).toNat ≤ Δ) :
    VSideAnm W M P n c d v (GwitAnm M P n)
      = -VfamAnm W P n c d v (wVAnm M n) γ₀ Γ Δ := by
  rw [VSideAnm_eq_gammaModeFinsum, VfamAnm_eq_finsum, ← Finset.sum_neg_distrib]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, VgammaModeCollAnm M P n (GwitAnm M P n) γ μ • W.smul d μ (W.smul c γ v))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    rw [← finsum_neg_distrib]
    refine finsum_congr fun μ => ?_
    rw [← neg_smul]
    congr 1
    rw [VgammaModeCollAnm_eq_towerCoeff M P n (GwitAnm M P n) (GwitAnm_spec M P n) (γ₀ + (g : ℤ)) μ]
    congr 1
    rw [towerCoeffAnm_pad P n (wVAnm M n (γ₀ + (g : ℤ))) ((n : ℤ) + 2 + (γ₀ + (g : ℤ))).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => wVAnm_vanish M n (γ₀ + (g : ℤ)) hδ)]
  · intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [VgammaModeCollAnm_zero_below M P n (GwitAnm M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact VSideAnm_gammaBody_zero_above W M P n c d v (GwitAnm M P n) hNc γ (by omega)

/-- **`AnmCircTowerEq` for all homogeneous `c, d`.**  `j`-free mirror of `LeftCircTowerEqn_holds`. -/
theorem AnmCircTowerEq_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (M P : ℕ) {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱) :
    AnmCircTowerEq W n M P c d v := by
  obtain ⟨Nd, hNd⟩ := W.regularity d v
  obtain ⟨Nc, hNc⟩ := W.regularity c v
  set γ₀ : ℤ := -((n : ℤ) + 1) with hγ₀
  set Γ : ℕ := (max Nd Nc - γ₀).toNat with hΓdef
  set Δ : ℕ := ((n : ℤ) + 2 + max (γ₀ + (Γ : ℤ)) 0).toNat with hΔdef
  have hmaxle : max Nd Nc ≤ γ₀ + (Γ : ℤ) := by
    have := Int.self_le_toNat (max Nd Nc - γ₀)
    rw [hΓdef]; omega
  have hΓU : Nd ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_left _ _) hmaxle
  have hΓV : Nc ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_right _ _) hmaxle
  refine AnmCircTowerEq_of_sides W n hc hd v (GwitAnm M P n)
    (fun i _ => GwitAnm_spec M P n i) (wUAnm P n) (wVAnm M n) γ₀ Γ Δ ?_ ?_
  · refine USideAnm_eq_UfamAnm W M P n c d v γ₀ Γ Δ hNd (le_refl _) hΓU ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega
  · refine VSideAnm_eq_neg_VfamAnm W M P n c d v γ₀ Γ Δ hNc (by rw [hγ₀]; omega) hΓV ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega

/-- **The Game-One `hcirc` field — closed.**  `∀ c d v, anmRight W n 0 (anmCirc W n 0 c d) v ∈
Onm W n 0`, from the universal tower predicate `AnmCircTowerEq_holds` via `hcirc_of_towerEq`. -/
theorem hcirc_closed (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ c d v : 𝒱, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0 :=
  hcirc_of_towerEq W n (fun M P c hc d hd v => AnmCircTowerEq_holds W n M P hc hd v)

/-- **`AnmRightModule W n` — closed.**  The Game-One `M(U)` `V`-action right-module closure
`O'_{n,0} *^n_0 𝒱 ⊆ O'_{n,0}`, from the universal tower predicate via `AnmRightModule_of_towerEq`. -/
theorem AnmRightModule_closed (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : AnmRightModule W n :=
  AnmRightModule_of_towerEq W n (fun M P c hc d hd v => AnmCircTowerEq_holds W n M P hc hd v)

end VOA
