/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmIdeal

/-!
# Game One — the `m = 0` Dong–Jiang circle keystone `Pres_mem_Onm` (shift-`0` mirror of `Pres_mem_On`).

This file builds the **shift-`0` higher-pole residue** `PresAnm W M n d` and its keystone membership
in the Dong–Jiang `m = 0` ideal `Onm W n 0` (`ZhuVermaAnArchAnmIdeal`).  It is the exact shift-`0`
mirror of the proven `Pres_mem_On` (`ZhuVermaAnDescent`), with the FZ shift `2n+2` of `circ W n`
replaced by the shift-`0` pole `n+2` of the `m = 0` circle generator
`anmCirc W n 0 u v = resHom W 0 (n+2) u v`.

## The shift-`0` higher-pole residue

`PresAnm W M n d u v := ∑_i C(M+d, i) · u₍ᵢ₋₍ₙ₊₂₎₋d₎ v = Res_z Y(u,z)v (1+z)^{M+d}/z^{n+2+d}`,
mode `i-(n+2)-d`, weight `cbz(M+d) i`.  At `d = 0` (homogeneous `u ∈ 𝒱_M`) it is exactly
`anmCirc W n 0 u v` (`PresAnm_zero`).

The integration-by-parts recursion is the pure-`cbz` upper-absorption identity
`(d+n+2)·C(M+d+1,i) = C(M+d+1,i)·(-(i-(n+2)-d)) + (M+d+1)·C(M+d,i-1)` (`presAnm_coeff_identity`),
which gives `(d+n+2)·PresAnm(d+1) = PresAnm_{L₋₁u}(d) + (M+d+1)·PresAnm(d)`
(`presAnm_recursion`).  Induction on `d` (base `d = 0` is `anmCirc_mem_Onm`) closes
`Pres_mem_Onm` for all `d`.

## What is proved here (axiom-clean)

* `PresAnm`, `PresAnm_zero` (the `d = 0` identification with `anmCirc W n 0`).
* `presAnm_coeff_identity` — the per-`i` upper-absorption scalar identity.
* `presAnm_recursion` — the integration-by-parts vector recursion.
* `Pres_mem_Onm` — **the keystone**: `PresAnm W M n d u v ∈ Onm W n 0` for homogeneous `u ∈ 𝒱_M`,
  all `d`.  Shift-`0` mirror of `Pres_mem_On`.

## What is proved (membership-criterion layer)

* `UfamAnm`/`VfamAnm` — the shift-`0` `PresAnm`-tower families (lifts of `UfamOn`/`VfamOn`).
* `UfamAnm_mem_Onm`/`VfamAnm_mem_Onm`/`UfamAnm_add_VfamAnm_mem_Onm` — they lie in `Onm W n 0` (via the
  keystone `Pres_mem_Onm`), for ANY weights.
* `AnmCircTowerEq` — the `m = 0` circle tower-decomposition predicate (shift-`0` lift of
  `RightCircTowerEq`).
* `anmRight_anmCirc_mem_Onm_of_tower_eq` — homogeneous membership criterion.
* `hcirc_of_towerEq` — the Game-One `hcirc` field for ALL `c, d, v` (homogeneous criterion +
  `reduce_homogeneous`); this is the exact input `ZhuVermaAnArchAnm.AnmRightModule_of_circ` /
  `ZhuVermaAnArchMU.MUGradedAction_of_gens` consume.
* `AnmRightModule_of_towerEq` — `AnmRightModule W n` from the universally-quantified tower predicate.

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) — the homogeneous tower predicate

`hcirc` is reduced to the single homogeneous predicate `AnmCircTowerEq W n M P c d v`: the shift-`0`
U/V master split of `anmRight W n 0 (anmCirc W n 0 c d) v = resHom W 0 (n+1) (resHom W 0 (n+2) c d) v`
into a `PresAnm`-tower U-family + V-family.  This is the shift-`0` (`s = 0`, pole `n+2` / `n+1`)
analogue of the proven shift-`n` chain `ZhuVermaAnDescent7→10/19/20/21` + `ZhuVermaAnArchL1`/`L1Close`
(`circ W n`, pole `2n+2`): the same Borcherds `iterate_term_rewrite` U/V split, base-mode ⊗ mode
reindex, and the two scalar tower-collapse cores, with the FZ shift `n` replaced by `0`.  Engine-true
on the rank-1 free boson (`certificates/mathematica/anmcirc_*.wl`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The shift-`0` higher-pole residue `PresAnm`. -/

/-- The shift-`0` depth-`d` higher-pole residue
`PresAnm W M n d u v = ∑_i C(M+d, i) · u₍ᵢ₋₍ₙ₊₂₎₋d₎ v = Res_z Y(u,z)v (1+z)^{M+d}/z^{n+2+d}`.
At `d = 0` it is `anmCirc W n 0 u v` for homogeneous `u ∈ 𝒱_M` (`PresAnm_zero`). -/
noncomputable def PresAnm (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (u v : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (M + d + 1),
    cbz ((M : ℤ) + d) (i : ℤ) • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d) v

/-- At `d = 0` the shift-`0` residue is the `m = 0` circle generator `anmCirc W n 0 u v`
(for homogeneous `u ∈ 𝒱_M`). -/
theorem PresAnm_zero (W : VertexOperatorAlgebra 𝒱) {M n : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    PresAnm W M n 0 u v = anmCirc W n 0 u v := by
  rw [anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 2) hu v, PresAnm]
  simp only [Nat.cast_zero, add_zero, sub_zero]
  rw [show (((M : ℤ)).toNat + 1) = M + 0 + 1 from by rw [Int.toNat_natCast]]

/-! ## The per-`i` integration-by-parts scalar identity (upper absorption). -/

/-- **The shift-`0` per-`i` upper-absorption identity** (engine/`FullSimplify`-verified):
`(d+n+2)·C(M+d+1,i) = C(M+d+1,i)·(-(i-(n+2)-d)) + (M+d+1)·C(M+d,i-1)`, all `M n d : ℕ`, `i : ℤ`.
This is `cbz_upper_absorption` at `K = M+d+1`: `i·C(M+d+1,i) = (M+d+1)·C(M+d,i-1)`. -/
theorem presAnm_coeff_identity (M n d : ℕ) (i : ℤ) :
    ((d : ℂ) + n + 2) * cbz ((M : ℤ) + d + 1) i
      = cbz ((M : ℤ) + d + 1) i * (-((i : ℂ) - ((n : ℂ) + 2) - d))
        + ((M : ℂ) + d + 1) * cbz ((M : ℤ) + d) (i - 1) := by
  have hua := cbz_upper_absorption (M + d + 1) i
  rw [show ((((M + d + 1 : ℕ)) : ℤ) - 1) = (M : ℤ) + d from by push_cast; ring,
      show (((M + d + 1 : ℕ)) : ℤ) = (M : ℤ) + d + 1 from by push_cast; ring] at hua
  push_cast at hua ⊢
  linear_combination hua

/-! ## The integration-by-parts vector recursion. -/

/-- **The shift-`0` integration-by-parts recursion** (mirror of the `Pres_mem_On` step):
`(d+n+2)·PresAnm(d+1) = PresAnm_{L₋₁u}(d) + (M+d+1)·PresAnm(d)`.  Both summands on the right lie in
`Onm W n 0` by the IH (the first applied to `L₋₁u ∈ 𝒱_{M+1}`). -/
theorem presAnm_recursion (W : VertexOperatorAlgebra 𝒱) (M n d : ℕ) (u v : 𝒱) :
    ((d : ℂ) + n + 2) • PresAnm W M n (d + 1) u v
      = PresAnm W (M + 1) n d (W.L (-1) u) v
        + ((M : ℂ) + d + 1) • PresAnm W M n d u v := by
  -- expand the `(L₋₁u)`-residue, on the common range `range (M+d+2)`, inner mode `i-(n+2)-d-1`.
  have hGeq : PresAnm W (M + 1) n d (W.L (-1) u) v
      = ∑ i ∈ Finset.range (M + d + 2),
          (cbz ((M : ℤ) + d + 1) (i : ℤ) * (-((i : ℂ) - ((n : ℂ) + 2) - d)))
            • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d - 1) v := by
    unfold PresAnm
    rw [show M + 1 + d + 1 = M + d + 2 from by ring]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast1 : (((M + 1 : ℕ) : ℤ)) + (d : ℤ) = (M : ℤ) + d + 1 := by push_cast; ring
    rw [hcast1, smul_L_neg_one W u v ((i : ℤ) - ((n : ℤ) + 2) - d),
      show ((i : ℤ) - ((n : ℤ) + 2) - d - 1) = (i : ℤ) - ((n : ℤ) + 2) - d - 1 from rfl,
      ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - ((n : ℤ) + 2) - d))
        (W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d - 1) v), smul_smul]
    congr 2
    push_cast
    ring
  -- LHS as a single range sum.
  have hLHS : ((d : ℂ) + n + 2) • PresAnm W M n (d + 1) u v
      = ∑ i ∈ Finset.range (M + d + 2),
          (((d : ℂ) + n + 2) * cbz ((M : ℤ) + (d + 1)) (i : ℤ))
            • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - (d + 1)) v := by
    unfold PresAnm
    rw [show M + (d + 1) + 1 = M + d + 2 from by ring, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul,
      show ((M : ℤ) + ((d + 1 : ℕ) : ℤ)) = (M : ℤ) + (d + 1) from by push_cast; ring,
      show ((i : ℤ) - ((n : ℤ) + 2) - ((d + 1 : ℕ) : ℤ)) = (i : ℤ) - ((n : ℤ) + 2) - (d + 1)
        from by push_cast; ring]
  -- the `(M+d+1)·PresAnm(d)` summand, shifted index, on the common range.
  have hPn : ((M : ℂ) + d + 1) • PresAnm W M n d u v
      = ∑ i ∈ Finset.range (M + d + 2),
          (((M : ℂ) + d + 1) * cbz ((M : ℤ) + d) ((i : ℤ) - 1))
            • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d - 1) v := by
    unfold PresAnm
    rw [Finset.smul_sum]
    rw [Finset.sum_range_succ' (fun i => (((M : ℂ) + d + 1) * cbz ((M : ℤ) + d) ((i : ℤ) - 1))
        • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - d - 1) v) (M + d + 1)]
    rw [show cbz ((M : ℤ) + d) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
    congr 2
    · push_cast; ring_nf
    · push_cast; ring_nf
  rw [hLHS, hGeq, hPn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul]
  congr 1
  · have h := presAnm_coeff_identity M n d (i : ℤ)
    rw [show ((M : ℤ) + (d + 1)) = (M : ℤ) + d + 1 from by push_cast; ring]
    push_cast at h ⊢
    linear_combination h
  · congr 1
    push_cast; ring

/-! ## The keystone `Pres_mem_Onm` (shift-`0` mirror of `Pres_mem_On`). -/

/-- **The keystone `Pres_mem_Onm`** (shift-`0` mirror of `Pres_mem_On`): for homogeneous `u ∈ 𝒱_M`
and every depth `d`, `PresAnm W M n d u v ∈ Onm W n 0`.

Induction on `d`: the base `d = 0` is `anmCirc W n 0 u v ∈ Onm W n 0` (`anmCirc_mem_Onm`); the step
uses the integration-by-parts recursion `(d+n+2)·PresAnm(d+1) = PresAnm_{L₋₁u}(d) +
(M+d+1)·PresAnm(d)` (both summands in `Onm` by the IH applied to `L₋₁u ∈ 𝒱_{M+1}` and to `u`),
dividing by the nonzero scalar `d+n+2`. -/
theorem Pres_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (d : ℕ) : PresAnm W M n d u v ∈ Onm W n 0 := by
  induction d generalizing M u with
  | zero =>
    rw [PresAnm_zero W hu v]; exact anmCirc_mem_Onm W n 0 u v
  | succ d ih =>
    have huL : W.L (-1) u ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W hu
    have hGmem : PresAnm W (M + 1) n d (W.L (-1) u) v ∈ Onm W n 0 := by
      have := ih (M := M + 1) (u := W.L (-1) u)
        (by rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring])
      exact this
    have hPmem : PresAnm W M n d u v ∈ Onm W n 0 := ih hu
    -- divide the recursion by the nonzero scalar `(d+n+2)`.
    have hscal : ((d : ℂ) + n + 2) ≠ 0 := by
      have hcast : ((d : ℂ) + n + 2) = ((d + n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast (by omega : d + n + 2 ≠ 0)
    have hrec := presAnm_recursion W M n d u v
    have hmem_rhs : PresAnm W (M + 1) n d (W.L (-1) u) v
        + ((M : ℂ) + d + 1) • PresAnm W M n d u v ∈ Onm W n 0 :=
      Submodule.add_mem _ hGmem (Submodule.smul_mem _ _ hPmem)
    have : PresAnm W M n (d + 1) u v
        = ((d : ℂ) + n + 2)⁻¹ • (((d : ℂ) + n + 2) • PresAnm W M n (d + 1) u v) := by
      rw [smul_smul, inv_mul_cancel₀ hscal, one_smul]
    rw [this, hrec]
    exact Submodule.smul_mem _ _ hmem_rhs

/-! ## Zero-handling helpers for the `m = 0` ingredients. -/

@[simp] theorem anmCirc_zero_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (d : 𝒱) :
    anmCirc W n m (0 : 𝒱) d = 0 := by
  have h := anmCirc_smul_left W n m (0 : ℂ) (0 : 𝒱) d
  rwa [zero_smul, zero_smul] at h

@[simp] theorem anmCirc_zero_right (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : 𝒱) :
    anmCirc W n m c (0 : 𝒱) = 0 := by
  have h := anmCirc_smul_right W n m (0 : ℂ) c (0 : 𝒱)
  rwa [zero_smul, zero_smul] at h

@[simp] theorem anmRight_zero_left' (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (v : 𝒱) :
    anmRight W n m (0 : 𝒱) v = 0 := by
  have h := anmRight_smul_left W n m (0 : ℂ) (0 : 𝒱) v
  rwa [zero_smul, zero_smul] at h

/-! ## The `PresAnm`-tower families and the `m = 0` circle tower-decomposition predicate.

Shift-`0` mirror of `UfamOn`/`VfamOn` (`ZhuVermaAnDescent8`).  The U-words of the master split of
`anmRight W n 0 (anmCirc W n 0 c d) v = resHom W 0 (n+1) (resHom W 0 (n+2) c d) v` are `c₍μ₎(d₍γ₎v)`
— exactly the modes of a `PresAnm`-tower in `c` based at `d₍γ₎v` — and the V-words are `d₍μ₎(c₍γ₎v)`
— a `PresAnm`-tower in `d` based at `c₍γ₎v`.  The keystone `Pres_mem_Onm` carries each tower into
`Onm W n 0`, so any finite ℂ-combination of them lies in `Onm W n 0`, regardless of the (dual-Hahn)
weights.  This is the shift-`0` lift of `UfamOn_mem_On`/`VfamOn_mem_On`/
`rightProd_circ_mem_On_of_tower_eq`. -/

/-- The shift-`0` **U-family** of `PresAnm`-towers (the `c`-first family): for weights
`wU : ℤ → ℕ → ℂ`, `∑_{g<Γ} ∑_{δ<Δ} wU (γ₀+g) δ • PresAnm W M n δ c (d₍γ₀+g₎v)`.  Shift-`0` lift of
`UfamOn`. -/
noncomputable def UfamAnm (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c d v : 𝒱)
    (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) : 𝒱 :=
  ∑ g ∈ Finset.range Γ, ∑ δ ∈ Finset.range Δ,
    wU (γ₀ + (g : ℤ)) δ • PresAnm W M n δ c (W.smul d (γ₀ + (g : ℤ)) v)

/-- The shift-`0` **V-family** of `PresAnm`-towers (the `d`-first family): for weights
`wV : ℤ → ℕ → ℂ`, `∑_{g<Γ} ∑_{δ<Δ} wV (γ₀+g) δ • PresAnm W P n δ d (c₍γ₀+g₎v)`.  Shift-`0` lift of
`VfamOn`. -/
noncomputable def VfamAnm (W : VertexOperatorAlgebra 𝒱) (P n : ℕ) (c d v : 𝒱)
    (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) : 𝒱 :=
  ∑ g ∈ Finset.range Γ, ∑ δ ∈ Finset.range Δ,
    wV (γ₀ + (g : ℤ)) δ • PresAnm W P n δ d (W.smul c (γ₀ + (g : ℤ)) v)

/-- **`UfamAnm` lies in `Onm W n 0`** (for homogeneous `c ∈ 𝒱_M`), by the keystone `Pres_mem_Onm`.
Shift-`0` lift of `UfamOn_mem_On`. -/
theorem UfamAnm_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d v : 𝒱) (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamAnm W M n c d v wU γ₀ Γ Δ ∈ Onm W n 0 := by
  refine Submodule.sum_mem _ (fun g _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_Onm W n hc (W.smul d (γ₀ + (g : ℤ)) v) δ)

/-- **`VfamAnm` lies in `Onm W n 0`** (for homogeneous `d ∈ 𝒱_P`), by the keystone `Pres_mem_Onm`.
Shift-`0` lift of `VfamOn_mem_On`. -/
theorem VfamAnm_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {P : ℕ} {d : 𝒱}
    (hd : d ∈ W.grading (P : ℤ)) (c v : 𝒱) (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    VfamAnm W P n c d v wV γ₀ Γ Δ ∈ Onm W n 0 := by
  refine Submodule.sum_mem _ (fun g _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_Onm W n hd (W.smul c (γ₀ + (g : ℤ)) v) δ)

/-- The combined U-family `+` V-family lies in `Onm W n 0`. -/
theorem UfamAnm_add_VfamAnm_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱)
    (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamAnm W M n c d v wU γ₀ Γ Δ + VfamAnm W P n c d v wV γ₀ Γ Δ ∈ Onm W n 0 :=
  Submodule.add_mem _ (UfamAnm_mem_Onm W n hc d v wU γ₀ Γ Δ)
    (VfamAnm_mem_Onm W n hd c v wV γ₀ Γ Δ)

/-- **The `m = 0` circle tower-decomposition predicate**: the residue-of-residue
`anmRight W n 0 (anmCirc W n 0 c d) v` equals a `PresAnm`-tower U-family in `c` (based at `d₍γ₎v`)
plus a `PresAnm`-tower V-family in `d` (based at `c₍γ₎v`).  Shift-`0` lift of `RightCircTowerEq`. -/
def AnmCircTowerEq (W : VertexOperatorAlgebra 𝒱) (n M P : ℕ) (c d v : 𝒱) : Prop :=
  ∃ (wU wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ),
    anmRight W n 0 (anmCirc W n 0 c d) v
      = UfamAnm W M n c d v wU γ₀ Γ Δ + VfamAnm W P n c d v wV γ₀ Γ Δ

/-- **The `m = 0` circle tower-collapse membership criterion** (homogeneous data).  For homogeneous
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`, if the residue-of-residue collapses onto the U/V `PresAnm`-tower families
(`AnmCircTowerEq`), then `anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0`.  Membership closed by the
keystone-backed `UfamAnm_add_VfamAnm_mem_Onm`.  Shift-`0` lift of
`rightProd_circ_mem_On_of_tower_eq`. -/
theorem anmRight_anmCirc_mem_Onm_of_tower_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ}
    {c d : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (v : 𝒱)
    (htow : AnmCircTowerEq W n M P c d v) :
    anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0 := by
  obtain ⟨wU, wV, γ₀, Γ, Δ, heq⟩ := htow
  rw [heq]
  exact UfamAnm_add_VfamAnm_mem_Onm W n hc hd v wU wV γ₀ Γ Δ

/-! ## Reducing the `hcirc` field (the Game-One target) to the homogeneous tower predicate.

`hcirc` for `AnmRightModule W n` (`ZhuVermaAnArchAnm`/`AnmRightModule_of_circ`) is
`∀ c d v, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0`.  Since `anmRight (·) v` and
`anmCirc (·) (·)` are ℂ-bilinear and vanish on negative gradings (`circ`/`resHom` bilinearity), the
general-`c,d` statement reduces to the homogeneous criterion above by `reduce_homogeneous`, exactly as
`hLcirc_of_towerEq` reduces (L1∘).  This isolates the one remaining input — the homogeneous tower
decomposition `AnmCircTowerEq` (the shift-`0` U/V scalar tower-collapse). -/

/-- **The Game-One `hcirc` field from the (universally-quantified) homogeneous tower predicate.**
Supplying `AnmCircTowerEq` for ALL grades `M, P` and homogeneous `c, d` discharges
`hcirc : ∀ c d v, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0` — the input
`AnmRightModule_of_circ` consumes to close `AnmRightModule W n`.  Shift-`0` lift of
`hLcirc_of_towerEq`. -/
theorem hcirc_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ v : 𝒱,
      AnmCircTowerEq W n M P c d v) :
    ∀ c d v : 𝒱, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0 := by
  intro c d v
  -- reduce `c` to homogeneous.
  refine reduce_homogeneous W
    (P := fun c => anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0) ?_ ?_ ?_ c
  · intro M c hc
    -- reduce `d` to homogeneous.
    refine reduce_homogeneous W
      (P := fun d => anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0) ?_ ?_ ?_ d
    · intro P d hd
      rcases lt_or_ge M 0 with hM | hM
      · rw [W.positivity M hM, Submodule.mem_bot] at hc
        subst hc
        rw [anmCirc_zero_left, anmRight_zero_left']
        exact (Onm W n 0).zero_mem
      rcases lt_or_ge P 0 with hP | hP
      · rw [W.positivity P hP, Submodule.mem_bot] at hd
        subst hd
        rw [anmCirc_zero_right, anmRight_zero_left']
        exact (Onm W n 0).zero_mem
      · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = (M' : ℤ) := ⟨M.toNat, by omega⟩
        obtain ⟨P', rfl⟩ : ∃ P' : ℕ, P = (P' : ℤ) := ⟨P.toNat, by omega⟩
        exact anmRight_anmCirc_mem_Onm_of_tower_eq W n hc hd v (Htow M' P' c hc d hd v)
    · show anmRight W n 0 (anmCirc W n 0 c (0 : 𝒱)) v ∈ Onm W n 0
      rw [anmCirc_zero_right, anmRight_zero_left']
      exact (Onm W n 0).zero_mem
    · intro x y hx hy
      show anmRight W n 0 (anmCirc W n 0 c (x + y)) v ∈ Onm W n 0
      rw [anmCirc_add_right, anmRight_add_left]
      exact (Onm W n 0).add_mem hx hy
  · show anmRight W n 0 (anmCirc W n 0 (0 : 𝒱) d) v ∈ Onm W n 0
    rw [anmCirc_zero_left, anmRight_zero_left']
    exact (Onm W n 0).zero_mem
  · intro x y hx hy
    show anmRight W n 0 (anmCirc W n 0 (x + y) d) v ∈ Onm W n 0
    rw [anmCirc_add_left, anmRight_add_left]
    exact (Onm W n 0).add_mem hx hy

/-- **The Game-One target reduced to `AnmRightModule W n`.**  From the universally-quantified
homogeneous tower predicate, the right-module closure `AnmRightModule W n`
(`O'_{n,0} *^n_0 𝒱 ⊆ O'_{n,0}`) holds: feed `hcirc_of_towerEq` to `AnmRightModule_of_circ`
(whose `hL` family is already closed unconditionally by `anmRight_zero_Lgen_mem_Onm`). -/
theorem AnmRightModule_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P : ℕ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ v : 𝒱,
      AnmCircTowerEq W n M P c d v) :
    AnmRightModule W n :=
  AnmRightModule_of_circ W n (hcirc_of_towerEq W n Htow)

end VOA
