/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchL1
import VOA.Modules.ZhuVermaAnDescent19
import VOA.Modules.ZhuVermaAnDescent20
import VOA.Modules.ZhuVermaAnDescent16

/-!
# (L1∘) closed — the two LEFT scalar cores and the full field `hLcirc_closed`.

This file discharges the two remaining scalar cores of `ZhuVermaAnArchL1` and assembles them, via
`LeftCircTowerEqn_of_sides`/`hLcirc_of_towerEq`, into the FULL left-circle ideal field

  `hLcirc_closed : ∀ c d b, leftProd W n (circ W n c d) b ∈ OnFull W n`.

## The LEFT cores vs the proven RIGHT cores

The LEFT collected scalars `UgammaModeCollLn`/`VgammaModeCollLn` (`ZhuVermaAnArchL1`) differ from the
proven RIGHT `UgammaModeColl`/`VgammaModeColl` (`ZhuVermaAnDescent10`) ONLY in the two FZ scalars:
`leftProd`'s `cbz(j+n,n)` (FZ) and `cbz(G_i+n,p)` (inner residue) replace `rightProd`'s `cbz(j+n,j)`
and `cbz(G_i+j,r)`.  Numerically the two collected scalars are NOT equal, so the RIGHT cores cannot be
reused by equality.  BUT the LEFT inner residue's top `G_i+n = M+P+2n+1-i` is **`j`-independent**,
which makes the collapse a clean mirror of the RIGHT chain (`ZhuVermaAnDescent19/20`): after the
`p`-collapse, `cbz_symm` reflection, and the `gBinom` peeling reflection, the per-`j` inner `i`-sum
collapses by the SAME `vandermonde_range_top`/`trinom_symm`/`IC_collapse`/`SR_collapse`/`tower_swap`/
`inner_lemma_range` machinery (the carrier is `P+n+1` not `P+n+1+j`, and the `j` now sits in the
middle's lower index `M+P-n-2-μ-γ-j`).  Every step is Mathematica-verified exact.

For the V-core the per-`(j,k)` kernel is LITERALLY Descent20's `VHkerJ M n j γ`, top-split from
carrier `P+n+1` (a `1`-Vandermonde) onto base `P+n`.

## Status: closed, axiom-clean `[propext, Classical.choice, Quot.sound]`

* `UgammaModeCollLn_eq_towerCoeff` / `VgammaModeCollLn_eq_towerCoeff` — the two scalar cores.
* `hLcirc_closed` — the assembled ideal field (via the L1 reduction `hLcirc_of_towerEq`).

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

/-! ## Step L-1 — the per-`(i,j)` direct LEFT scalars (`p`-eliminated, guard/peeling reflected). -/

/-- The per-`(i,j)` direct LEFT U-scalar: `UgammaCoeffLn` with `p` substituted by `rSub`, the
peeling factor reflected to `cbz(-μ-1, (i-2n-2)-μ)` (`uIter_eq_cbz`), and the FZ scalar carried as
`cbz(j+n,n)`; the inner residue's top is the `j`-independent `G_i+n`. -/
noncomputable def directUCoeffLn (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
    * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        then cbz ((G i : ℤ) + n) (rSub n i j γ μ) else 0)
    * cbz (-μ - 1) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ)

/-- The per-`(i,j)` direct LEFT V-scalar. -/
noncomputable def directVCoeffLn (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ))
      * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
          then cbz ((G i : ℤ) + n) (rSub n i j γ μ) else 0)
      * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-- **Matched-term identity (LEFT U).**  When `(p : ℤ) = rSub n i j γ μ`, the LEFT mode-iterate
coefficient `UgammaCoeffLn M P n G i j p γ` equals `directUCoeffLn M P n G i j γ μ`. -/
theorem UgammaCoeffLn_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ μ : ℤ)
    (hr : (p : ℤ) = rSub n i j γ μ) :
    UgammaCoeffLn M P n G i j p γ = directUCoeffLn M P n G i j γ μ := by
  have hN : (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) = γ + (μ - ((i : ℤ) - 2 * (n : ℤ) - 2)) := by
    rw [hr, rSub]; ring
  have hdiff : γ - ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) = ((i : ℤ) - 2 * (n : ℤ) - 2) - μ := by
    rw [hN]; ring
  rw [UgammaCoeffLn, directUCoeffLn, assemblyLeadLn]
  by_cases hguard : (p : ℤ) - ((n : ℤ) + (j : ℤ) + 1) ≤ γ
  · rw [if_pos hguard, hdiff]
    -- rewrite the peeling factor via `uIter_eq_cbz`.
    have hmu : μ ≤ (i : ℤ) - 2 * (n : ℤ) - 2 := by rw [hN] at hguard; omega
    have hpeel : ((-1 : ℂ) ^ (((i : ℤ) - 2 * (n : ℤ) - 2) - μ).toNat
          * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ).toNat)
        = cbz (-μ - 1) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ) := by
      have := uIter_eq_cbz ((i : ℤ) - 2 * (n : ℤ) - 2) μ
      rwa [if_pos hmu] at this
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, if_pos hgr, hpeel, show (p : ℤ) = rSub n i j γ μ from hr]
    · rw [if_neg hgr, if_neg hgr, hpeel]; ring
  · rw [if_neg hguard]
    -- guard fails ⇔ `μ > (i-2n-2)`, so the reflected `cbz` lower index is `< 0`.
    have hmu : (i : ℤ) - 2 * (n : ℤ) - 2 - μ < 0 := by rw [hN] at hguard; omega
    rw [cbz_apply_neg (-μ - 1) hmu]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr]; ring
    · rw [if_neg hgr]; ring

/-- **Matched-term identity (LEFT V).** -/
theorem VgammaCoeffLn_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ μ : ℤ)
    (hr : (p : ℤ) = rSub n i j γ μ) :
    VgammaCoeffLn M P n G i j p γ = directVCoeffLn M P n G i j γ μ := by
  rw [VgammaCoeffLn, directVCoeffLn, assemblyLeadLn]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    have hpeel : ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat)
        = cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ := by
      have := vIter_core ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat
      have hγn : (γ.toNat : ℤ) = γ := Int.toNat_of_nonneg hγ
      rw [this, show ((γ.toNat : ℤ) - 1 - ((i : ℤ) - 2 * (n : ℤ) - 2))
            = γ + 2 * (n : ℤ) + 1 - (i : ℤ) from by rw [hγn]; ring, hγn]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, if_pos hgr, hpeel, show (p : ℤ) = rSub n i j γ μ from hr]
    · rw [if_neg hgr, if_neg hgr, hpeel]; ring
  · rw [if_neg hγ, if_neg hγ]

/-! ## Step L-2 — the per-`(i,j)` inner `p`-finset collapse onto the substituted index. -/

/-- **Inner `p`-finset collapse (LEFT U).** -/
theorem UinnerLn_collapse (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (hj : j ≤ n) :
    (∑ p ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then UgammaCoeffLn M P n G i j p γ else 0))
      = directUCoeffLn M P n G i j γ μ := by
  have hcond : ∀ p : ℕ,
      (μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
        ↔ ((p : ℤ) = rSub n i j γ μ) := by
    intro p; rw [rSub]; constructor <;> intro h <;> omega
  rw [Finset.sum_congr rfl fun p _ => by rw [show (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ then UgammaCoeffLn M P n G i j p γ else 0)
      = (if (p : ℤ) = rSub n i j γ μ then UgammaCoeffLn M P n G i j p γ else 0) from by
        simp only [hcond p]]]
  by_cases hpos : 0 ≤ rSub n i j γ μ
  · set p₀ : ℕ := (rSub n i j γ μ).toNat with hp₀
    have hp₀cast : (p₀ : ℤ) = rSub n i j γ μ := by rw [hp₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : p₀ ∈ Finset.range (G i + n + 1)
    · rw [Finset.sum_eq_single_of_mem p₀ hmem
        (fun p _ hne => by
          rw [if_neg (by
            intro hc; exact hne (by
              have : (p : ℤ) = (p₀ : ℤ) := by rw [hp₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hp₀cast, UgammaCoeffLn_at_rSub M P n G i j p₀ γ μ hp₀cast]
    · have hgt : (G i : ℤ) + n < rSub n i j γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + n + 1 ≤ p₀ := by omega
        have hle : ((G i + n + 1 : ℕ) : ℤ) ≤ (p₀ : ℤ) := by exact_mod_cast this
        rw [hp₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun p hp => by
        rw [if_neg (by
          rw [Finset.mem_range] at hp
          intro hc
          have hple : p ≤ G i + n := by omega
          have hle : (p : ℤ) ≤ (G i : ℤ) + n := by exact_mod_cast hple
          rw [hc] at hle; omega)]]
      rw [directUCoeffLn]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
      · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ) + n) (by rw [hG hgr]; omega)
          (Or.inr (by omega))]; ring
      · rw [if_neg hgr]; ring
  · replace hpos : rSub n i j γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun p _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
        rw [hc] at this; omega)]]
    rw [directUCoeffLn]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ) + n) (by omega)]; ring
    · rw [if_neg hgr]; ring

/-- **Inner `p`-finset collapse (LEFT V).** -/
theorem VinnerLn_collapse (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (hj : j ≤ n) :
    (∑ p ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then VgammaCoeffLn M P n G i j p γ else 0))
      = directVCoeffLn M P n G i j γ μ := by
  have hcond : ∀ p : ℕ,
      (μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
        ↔ ((p : ℤ) = rSub n i j γ μ) := by
    intro p; rw [rSub]; constructor <;> intro h <;> omega
  rw [Finset.sum_congr rfl fun p _ => by rw [show (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2)
        + ((p : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ then VgammaCoeffLn M P n G i j p γ else 0)
      = (if (p : ℤ) = rSub n i j γ μ then VgammaCoeffLn M P n G i j p γ else 0) from by
        simp only [hcond p]]]
  by_cases hpos : 0 ≤ rSub n i j γ μ
  · set p₀ : ℕ := (rSub n i j γ μ).toNat with hp₀
    have hp₀cast : (p₀ : ℤ) = rSub n i j γ μ := by rw [hp₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : p₀ ∈ Finset.range (G i + n + 1)
    · rw [Finset.sum_eq_single_of_mem p₀ hmem
        (fun p _ hne => by
          rw [if_neg (by
            intro hc; exact hne (by
              have : (p : ℤ) = (p₀ : ℤ) := by rw [hp₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hp₀cast, VgammaCoeffLn_at_rSub M P n G i j p₀ γ μ hp₀cast]
    · have hgt : (G i : ℤ) + n < rSub n i j γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + n + 1 ≤ p₀ := by omega
        have hle : ((G i + n + 1 : ℕ) : ℤ) ≤ (p₀ : ℤ) := by exact_mod_cast this
        rw [hp₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun p hp => by
        rw [if_neg (by
          rw [Finset.mem_range] at hp
          intro hc
          have hple : p ≤ G i + n := by omega
          have hle : (p : ℤ) ≤ (G i : ℤ) + n := by exact_mod_cast hple
          rw [hc] at hle; omega)]]
      rw [directVCoeffLn]
      by_cases hγ : 0 ≤ γ
      · rw [if_pos hγ]
        by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ) + n) (by rw [hG hgr]; omega)
            (Or.inr (by omega))]; ring
        · rw [if_neg hgr]; ring
      · rw [if_neg hγ]
  · replace hpos : rSub n i j γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun p _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
        rw [hc] at this; omega)]]
    rw [directVCoeffLn]
    by_cases hγ : 0 ≤ γ
    · rw [if_pos hγ]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
      · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ) + n) (by omega)]; ring
      · rw [if_neg hgr]; ring
    · rw [if_neg hγ]

/-! ## Step L-3 — `UgammaModeCollLn`/`VgammaModeCollLn` as the direct `(i,j)`-double sum. -/

/-- **`UgammaModeCollLn` in the direct `(i,j)` frame.** -/
theorem UgammaModeCollLn_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeCollLn M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directUCoeffLn M P n G i j γ μ := by
  rw [UgammaModeCollLn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact UinnerLn_collapse M P n G i j γ μ (hG i) (by have := Finset.mem_range.mp hj; omega)

/-- **`VgammaModeCollLn` in the direct `(i,j)` frame.** -/
theorem VgammaModeCollLn_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeCollLn M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directVCoeffLn M P n G i j γ μ := by
  rw [VgammaModeCollLn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact VinnerLn_collapse M P n G i j γ μ (hG i) (by have := Finset.mem_range.mp hj; omega)

/-! ## Step L-4 — the per-`j` inner `i`-sums `InnerILn`/`VInnerILn` and the `j`-sum reductions.

The LEFT mirror of `ZhuVermaAnDescent19.UgammaModeColl_eq_jSum`/`ZhuVermaAnDescent20.VgammaModeColl_eq_jSum`.
The middle binomial `cbz(G_i+n, rSub)` is reflected by `ZhuMu.cbz_symm` (top `G_i+n` a `ℕ`-cast, hence
`≥ 0`) to the `i`-INDEPENDENT-lower-index frame `cbz((M+P+2n+1)-i, M+P-n-2-μ-γ-j)`, and the FZ scalar
`cbz(j+n,n)` is restored to `cbz(j+n,j)` via `ZhuMu.cbz_symm` (so the proven `ZhuVermaAnDescent19/20`
weights apply verbatim). -/

/-- The LEFT per-`j` inner `i`-sum (U).  Middle top `(M+P+3n+1)-i = (G_i+n)`, `i`-independent lower
index `M+P-2-μ-γ-j`. -/
noncomputable def InnerILn (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1),
    cbz ((M : ℤ) + n) (i : ℤ)
      * cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
      * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)

/-- The LEFT per-`j` inner `i`-sum (V), `i`-independent middle lower index, sign normalized. -/
noncomputable def VInnerILn (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (M + n + 1),
    cbz ((M : ℤ) + n) (i : ℤ)
      * cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
      * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)

/-- **`UgammaModeCollLn` as the `j`-sum of `InnerILn`** (LEFT lift of `UgammaModeColl_eq_jSum`). -/
theorem UgammaModeCollLn_eq_jSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeCollLn M P n G γ μ
      = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * InnerILn M P n j γ μ := by
  rw [UgammaModeCollLn_eq_directSum M P n G hG γ μ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [InnerILn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
  have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := ucore_guard M P n i hile
  rw [directUCoeffLn, if_pos hgr]
  -- reflect the FZ scalar `cbz(j+n,n) = cbz(j+n,j)`.
  rw [show cbz ((j : ℤ) + n) (n : ℤ) = cbz ((j : ℤ) + n) (j : ℤ) from by
        rw [show (j : ℤ) + n = ((j + n : ℕ) : ℤ) from by push_cast; ring,
          ZhuMu.cbz_symm (j + n) (j : ℤ)]
        congr 1; push_cast; ring]
  -- reflect the middle binomial: top `G_i+n` is a `ℕ`-cast, hence `≥ 0`.
  have hmid : cbz ((G i : ℤ) + n) (rSub n i j γ μ)
      = cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j) := by
    rw [show (G i : ℤ) + n = ((G i + n : ℕ) : ℤ) from by push_cast; ring,
      ZhuMu.cbz_symm (G i + n) (rSub n i j γ μ),
      show ((G i + n : ℕ) : ℤ) = (G i : ℤ) + n from by push_cast; ring, hG i hgr, rSub]
    congr 1 <;> ring
  rw [hmid]
  ring

/-- **`VgammaModeCollLn` as the `j`-sum of `VInnerILn`** (LEFT lift of `VgammaModeColl_eq_jSum`). -/
theorem VgammaModeCollLn_eq_jSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeCollLn M P n G γ μ
      = if 0 ≤ γ then
          ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * VInnerILn M P n j γ μ
        else 0 := by
  rw [VgammaModeCollLn_eq_directSum M P n G hG γ μ]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [VInnerILn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
    have hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 := ucore_guard M P n i hile
    rw [directVCoeffLn, if_pos hγ, if_pos hgr, vsign_eq n i]
    rw [show cbz ((j : ℤ) + n) (n : ℤ) = cbz ((j : ℤ) + n) (j : ℤ) from by
          rw [show (j : ℤ) + n = ((j + n : ℕ) : ℤ) from by push_cast; ring,
            ZhuMu.cbz_symm (j + n) (j : ℤ)]
          congr 1; push_cast; ring]
    have hmid : cbz ((G i : ℤ) + n) (rSub n i j γ μ)
        = cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j) := by
      rw [show (G i : ℤ) + n = ((G i + n : ℕ) : ℤ) from by push_cast; ring,
        ZhuMu.cbz_symm (G i + n) (rSub n i j γ μ),
        show ((G i + n : ℕ) : ℤ) = (G i : ℤ) + n from by push_cast; ring, hG i hgr, rSub]
      congr 1 <;> ring
    rw [hmid]
    ring
  · rw [if_neg hγ]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [directVCoeffLn, if_neg hγ]

/-! ## Step L-5 — the U-core inner `i`-sum collapse `InnerILn → towerCoeff`.

Faithful mirror of `ZhuVermaAnDescent19` (`InnerI_eq_ASum`/`ASum_eq_kFinsum`/`InnerI_tower`) with the
carrier `P+2n+1` (from `(M+P+3n+1)-i = (M+n-i)+(P+2n+1)`) and the `j`-shifted kernel `HkerLn`. -/

/-- The LEFT U `a`-sum (R3-Ln's RHS). -/
noncomputable def ASumLn (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range (M + n + 1),
    cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
      * cbz ((M : ℤ) + n) (a : ℤ)
      * cbz ((M : ℤ) + n - a - μ - 1) ((M : ℤ) - n - 2 - μ - a)

/-- **R3-Ln** (`InnerILn = ASumLn`).  Vandermonde top-split of the middle binomial
`C((M+P+3n+1)-i, K0) = ∑_a C(M+n-i, a)·C(P+2n+1, K0-a)`, swap to `a`-outer, factor, `IC_collapse`. -/
theorem InnerILn_eq_ASumLn (M P n j : ℕ) (γ μ : ℤ) :
    InnerILn M P n j γ μ = ASumLn M P n j γ μ := by
  rw [InnerILn, ASumLn]
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ)
              * cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
              * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)
        = ∑ i ∈ Finset.range (M + n + 1), ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
              * (cbz ((M : ℤ) + n) (i : ℤ) * cbz (((M : ℤ) + n) - (i : ℤ)) (a : ℤ)
                  * cbz (-μ - 1) ((i : ℤ) - 2 * n - 2 - μ)) from
      Finset.sum_congr rfl fun i hi => ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [← Finset.mul_sum, IC_collapse M n a μ hale]
    ring
  · have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
    have hmid : cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((M + n - i : ℕ) : ℤ) (a : ℤ)
              * cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a) := by
      rw [vandermonde_range_top (M + n - i) ((P : ℤ) + 2 * n + 1)
        ((M : ℤ) + P - 2 - μ - γ - j) (N := M + n + 1) (by omega)]
      congr 1
      rw [Nat.cast_sub hile]; push_cast; ring
    rw [hmid, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((M + n - i : ℕ) : ℤ) = (M : ℤ) + n - i from by rw [Nat.cast_sub hile]; push_cast; ring]
    ring

/-- The LEFT U per-`(j,k)` weight kernel `HkerLn_j(k) = C(P+2n+1, k+P+n-γ-j)·C(2n+1+k, k)`. -/
noncomputable def HkerLn (P n j : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz ((P : ℤ) + 2 * n + 1) (k + P + n - γ - j) * cbz (2 * (n : ℤ) + 1 + k) k

/-- **`ASumLn` as a `cbz(M+n, (μ+2n+2)+k)`-finsum** (mirror of `ASum_eq_kFinsum`). -/
theorem ASumLn_eq_kFinsum (M P n j : ℕ) (γ μ : ℤ) :
    ASumLn M P n j γ μ
      = ∑ᶠ k : ℤ, cbz ((M : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k) * HkerLn P n j γ k := by
  rw [ASumLn]
  rw [← Finset.sum_range_reflect
      (fun a => cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
          * cbz ((M : ℤ) + n) (a : ℤ)
          * cbz ((M : ℤ) + n - a - μ - 1) ((M : ℤ) - n - 2 - μ - a)) (M + n + 1)]
  rw [show (∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - ((M + n + 1 - 1 - a : ℕ) : ℤ))
                * cbz ((M : ℤ) + n) ((M + n + 1 - 1 - a : ℕ) : ℤ)
                * cbz ((M : ℤ) + n - ((M + n + 1 - 1 - a : ℕ) : ℤ) - μ - 1)
                    ((M : ℤ) - n - 2 - μ - ((M + n + 1 - 1 - a : ℕ) : ℤ)))
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (a : ℤ)
              * (cbz ((P : ℤ) + 2 * n + 1) (((P : ℤ) - n - 2 - μ - γ - j) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)) from
      Finset.sum_congr rfl fun a ha => ?_]
  · rw [show (∑ a ∈ Finset.range (M + n + 1),
              cbz ((M : ℤ) + n) (a : ℤ)
                * (cbz ((P : ℤ) + 2 * n + 1) (((P : ℤ) - n - 2 - μ - γ - j) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))
          = ∑ᶠ a : ℤ, cbz ((M : ℤ) + n) a
                * (cbz ((P : ℤ) + 2 * n + 1) (((P : ℤ) - n - 2 - μ - γ - j) + a)
                    * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)) from ?_]
    · rw [← finsum_comp_equiv (Equiv.addLeft ((μ : ℤ) + 2 * n + 2))
          (f := fun a : ℤ => cbz ((M : ℤ) + n) a
              * (cbz ((P : ℤ) + 2 * n + 1) (((P : ℤ) - n - 2 - μ - γ - j) + a)
                  * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))]
      simp only [Equiv.coe_addLeft]
      refine finsum_congr fun k => ?_
      rw [HkerLn,
        show ((μ : ℤ) + 2 * n + 2 + k) = (μ : ℤ) + 2 * (n : ℤ) + 2 + k from by ring,
        show ((P : ℤ) - n - 2 - μ - γ - j) + ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) = k + P + n - γ - j from by ring,
        show ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) - μ - 1 = 2 * (n : ℤ) + 1 + k from by ring,
        show ((μ : ℤ) + 2 * (n : ℤ) + 2 + k) - 2 * n - 2 - μ = k from by ring]
    · refine (finsumZ_eq_range_sum (N := M + n + 1)
        (fun a : ℤ => cbz ((M : ℤ) + n) a
            * (cbz ((P : ℤ) + 2 * n + 1) (((P : ℤ) - n - 2 - μ - γ - j) + a)
                * cbz ((a : ℤ) - μ - 1) ((a : ℤ) - 2 * n - 2 - μ)))
        (fun p hp => by dsimp only; rw [cbz_apply_neg ((M : ℤ) + n) hp, zero_mul])
        (fun p hp => by
          dsimp only
          rw [cbz_lt (by positivity) (by
            have : (M + n + 1 : ℤ) ≤ p := by exact_mod_cast hp
            omega), zero_mul])).symm
  · have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [show M + n + 1 - 1 - a = M + n - a from by omega]
    have hca : (((M + n - a : ℕ) : ℤ)) = (M : ℤ) + n - a := by rw [Nat.cast_sub hale]; push_cast; ring
    rw [hca]
    rw [show cbz ((M : ℤ) + n) ((M : ℤ) + n - a)
          = cbz ((M : ℤ) + n) (a : ℤ) from by
        rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring,
          ← ZhuMu.cbz_symm (M + n) (a : ℤ)]]
    rw [show ((M : ℤ) + P - 2 - μ - γ - j) - ((M : ℤ) + n - a)
          = ((P : ℤ) - n - 2 - μ - γ - j) + a from by ring,
      show (M : ℤ) + n - ((M : ℤ) + n - a) - μ - 1 = (a : ℤ) - μ - 1 from by ring,
      show (M : ℤ) - n - 2 - μ - ((M : ℤ) + n - a) = (a : ℤ) - 2 * n - 2 - μ from by ring]
    ring

/-- `HkerLn` vanishes for `k < 0` (the `C(2n+1+k, k)` factor). -/
theorem HkerLn_lo (P n j : ℕ) (γ : ℤ) {k : ℤ} (hk : k < 0) : HkerLn P n j γ k = 0 := by
  rw [HkerLn, cbz_apply_neg (2 * (n : ℤ) + 1 + k) hk, mul_zero]

/-- `HkerLn` vanishes for `2n+2+γ ≤ k` when `j ≤ n` (the `C(P+2n+1, k+P+n-γ-j)` factor). -/
theorem HkerLn_hi (P n j : ℕ) (γ : ℤ) (hjn : j ≤ n) {k : ℤ} (hk : 2 * (n : ℤ) + 2 + γ ≤ k) :
    HkerLn P n j γ k = 0 := by
  have hjn' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjn
  rw [HkerLn, cbz_lt (by positivity) (by omega : (P : ℤ) + 2 * n + 1 < k + P + n - γ - j), zero_mul]

/-- The LEFT U per-`j` tower weight (`tower_swap` weight at base `M+n`):
`wtJLn(δ) = ∑_{k<Δ} (-1)^(k-δ)·C(k,δ)·HkerLn(k)`. -/
noncomputable def wtJLn (P n j : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (2 * n + 2 + γ).toNat,
    (-1 : ℂ) ^ (k - ν) * cbz (k : ℤ) (ν : ℤ) * HkerLn P n j γ (k : ℤ)

/-- **Per-`j` `InnerILn` tower collapse** (grade `M`).  Via `InnerILn_eq_ASumLn`, `ASumLn_eq_kFinsum`,
`tower_swap` (base `M+n`, support `[0,Δ)` from `HkerLn_lo`/`HkerLn_hi`). -/
theorem InnerILn_tower (M P n j : ℕ) (γ μ : ℤ) (hjn : j ≤ n) :
    InnerILn M P n j γ μ
      = ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
          wtJLn P n j γ ν * cbz ((M : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) := by
  rw [InnerILn_eq_ASumLn, ASumLn_eq_kFinsum]
  rw [show (∑ᶠ k : ℤ, cbz ((M : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k) * HkerLn P n j γ k)
        = ∑ᶠ k : ℤ, cbz (((M + n : ℕ)) : ℤ) (((μ : ℤ) + 2 * n + 2) + k) * HkerLn P n j γ k from by
      push_cast; rfl]
  rw [tower_swap (M + n) (μ + 2 * n + 2) (HkerLn P n j γ) (2 * n + 2 + γ).toNat
      (fun k hk => HkerLn_lo P n j γ hk)
      (fun k hk => HkerLn_hi P n j γ hjn (by
        have hh : ((2 * n + 2 + γ).toNat : ℤ) ≤ k := hk
        rcases lt_or_ge (2 * (n : ℤ) + 2 + γ) 0 with h | h
        · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
        · rw [Int.toNat_of_nonneg h] at hh; omega))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [wtJLn]
  congr 2

/-- **The depth-`n` LEFT U-core weights** `wULn(P,n,γ,δ) = ∑_{j≤n} (-1)^j C(j+n,j)·wtJLn(P,n,j,γ,δ)`. -/
noncomputable def wULn (P n : ℕ) (γ : ℤ) (δ : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * wtJLn P n j γ δ

/-- **The LEFT U-core scalar collapse.**  `UgammaModeCollLn` equals the grade-`M` `towerCoeff` tower
with the `M`-independent weights `wULn` and depth `Δ = (2n+2+γ).toNat`. -/
theorem UgammaModeCollLn_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeCollLn M P n G γ μ
      = towerCoeff M n (wULn P n γ) (2 * n + 2 + γ).toNat μ := by
  rw [UgammaModeCollLn_eq_jSum M P n G hG γ μ, towerCoeff]
  rw [show ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * InnerILn M P n j γ μ
        = ∑ j ∈ Finset.range (n + 1), ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * wtJLn P n j γ ν)
              * cbz ((M : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) from
      Finset.sum_congr rfl fun j hj => by
        rw [InnerILn_tower M P n j γ μ (by have := Finset.mem_range.mp hj; omega), Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => by ring,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [wULn, Finset.sum_mul]

/-! ## Step L-6 — the V-core inner `i`-sum collapse `VInnerILn → towerCoeff` (grade `P`).

Faithful mirror of `ZhuVermaAnDescent20`: carrier `P+2n+1` (from `(M+P+3n+1)-i = (M+n-i)+(P+2n+1)`),
the kernel `VHkerLn`, and the `(n+1)`-Vandermonde top-split to base `P+n` (`GvLn`). -/

/-- The LEFT V `a`-sum. -/
noncomputable def VASumLn (M P n j : ℕ) (γ μ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range (M + n + 1),
    cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
      * cbz ((M : ℤ) + n) (a : ℤ)
      * cbz (γ + (n : ℤ) + 1 - M + a) (γ - M - n + a)

/-- **R3-V-Ln** (`VInnerILn = VASumLn`). -/
theorem VInnerILn_eq_VASumLn (M P n j : ℕ) (γ μ : ℤ) :
    VInnerILn M P n j γ μ = VASumLn M P n j γ μ := by
  rw [VInnerILn, VASumLn]
  rw [show ∑ i ∈ Finset.range (M + n + 1),
            cbz ((M : ℤ) + n) (i : ℤ)
              * cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
              * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)
        = ∑ i ∈ Finset.range (M + n + 1), ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
              * (cbz ((M : ℤ) + n) (i : ℤ) * cbz (((M : ℤ) + n) - (i : ℤ)) (a : ℤ)
                  * ((-1 : ℂ) ^ i * cbz (γ + 2 * (n : ℤ) + 1 - i) γ)) from
      Finset.sum_congr rfl fun i hi => ?_]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [← Finset.mul_sum, VIC_collapse M n a γ hale]
    ring
  · have hile : i ≤ M + n := by have := Finset.mem_range.mp hi; omega
    have hmid : cbz (((M : ℤ) + P + 3 * n + 1) - i) ((M : ℤ) + P - 2 - μ - γ - j)
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((M + n - i : ℕ) : ℤ) (a : ℤ)
              * cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a) := by
      rw [vandermonde_range_top (M + n - i) ((P : ℤ) + 2 * n + 1)
        ((M : ℤ) + P - 2 - μ - γ - j) (N := M + n + 1) (by omega)]
      congr 1
      rw [Nat.cast_sub hile]; push_cast; ring
    rw [hmid, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ((M + n - i : ℕ) : ℤ) = (M : ℤ) + n - i from by rw [Nat.cast_sub hile]; push_cast; ring]
    ring

/-- The LEFT V per-`(j,k)` kernel `VHkerLn_j(k) = C(M+n, b)·C(γ+2n+1-b, γ-b)`, `b = (n+1+γ+j)-k`. -/
noncomputable def VHkerLn (M n j : ℕ) (γ : ℤ) (k : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) (((n : ℤ) + 1 + γ + j) - k)
    * cbz (γ + 2 * (n : ℤ) + 1 - (((n : ℤ) + 1 + γ + j) - k)) (γ - (((n : ℤ) + 1 + γ + j) - k))

/-- **`VASumLn` as a `cbz(P+2n+1, s+k)`-finsum.** -/
theorem VASumLn_eq_kFinsum (M P n j : ℕ) (γ μ : ℤ) :
    VASumLn M P n j γ μ
      = ∑ᶠ k : ℤ, cbz ((P : ℤ) + 2 * n + 1) (((μ : ℤ) + 2 * n + 2) + k) * VHkerLn M n j γ k := by
  rw [VASumLn]
  rw [← Finset.sum_range_reflect
      (fun a => cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - a)
          * cbz ((M : ℤ) + n) (a : ℤ)
          * cbz (γ + (n : ℤ) + 1 - M + a) (γ - M - n + a)) (M + n + 1)]
  rw [show (∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + 2 * n + 1) (((M : ℤ) + P - 2 - μ - γ - j) - ((M + n + 1 - 1 - a : ℕ) : ℤ))
                * cbz ((M : ℤ) + n) ((M + n + 1 - 1 - a : ℕ) : ℤ)
                * cbz (γ + (n : ℤ) + 1 - M + ((M + n + 1 - 1 - a : ℕ) : ℤ))
                    (γ - M - n + ((M + n + 1 - 1 - a : ℕ) : ℤ)))
        = ∑ a ∈ Finset.range (M + n + 1),
            cbz ((P : ℤ) + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)
              * (cbz ((M : ℤ) + n) (a : ℤ)
                  * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from
      Finset.sum_congr rfl fun a ha => ?_]
  · rw [show (∑ a ∈ Finset.range (M + n + 1),
              cbz ((P : ℤ) + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)
                * (cbz ((M : ℤ) + n) (a : ℤ)
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
          = ∑ᶠ a : ℤ, cbz ((P : ℤ) + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from ?_]
    · rw [show (∑ᶠ a : ℤ, cbz ((P : ℤ) + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
            = ∑ᶠ a : ℤ, cbz ((P : ℤ) + 2 * n + 1)
                  (((μ : ℤ) + 2 * n + 2) + (((n : ℤ) + 1 + γ + j) - a))
                * (cbz ((M : ℤ) + n) a
                    * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)) from
        finsum_congr fun a => by
          rw [show ((P : ℤ) + 2 * n + 1) = (((P + 2 * n + 1 : ℕ)) : ℤ) from by push_cast; ring,
            ZhuMu.cbz_symm (P + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)]
          congr 2
          push_cast; ring]
      rw [← finsum_comp_equiv (Equiv.subLeft ((n : ℤ) + 1 + γ + j))
          (f := fun a : ℤ => cbz ((P : ℤ) + 2 * n + 1)
                (((μ : ℤ) + 2 * n + 2) + (((n : ℤ) + 1 + γ + j) - a))
              * (cbz ((M : ℤ) + n) a
                  * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))]
      simp only [Equiv.subLeft_apply]
      refine finsum_congr fun k => ?_
      rw [VHkerLn,
        show ((n : ℤ) + 1 + γ + j) - (((n : ℤ) + 1 + γ + j) - k) = k from by ring]
    · refine (finsumZ_eq_range_sum (N := M + n + 1)
        (fun a : ℤ => cbz ((P : ℤ) + 2 * n + 1) ((P : ℤ) - n - 2 - μ - γ - j + a)
            * (cbz ((M : ℤ) + n) a
                * cbz (γ + 2 * (n : ℤ) + 1 - a) (γ - a)))
        (fun p hp => by dsimp only; rw [cbz_apply_neg ((M : ℤ) + n) hp]; ring)
        (fun p hp => by
          dsimp only
          rw [cbz_lt (by positivity) (by
            have : (M + n + 1 : ℤ) ≤ p := by exact_mod_cast hp
            omega : (M : ℤ) + n < p)]; ring)).symm
  · have hale : a ≤ M + n := by have := Finset.mem_range.mp ha; omega
    rw [show M + n + 1 - 1 - a = M + n - a from by omega]
    have hca : (((M + n - a : ℕ) : ℤ)) = (M : ℤ) + n - a := by rw [Nat.cast_sub hale]; push_cast; ring
    rw [hca]
    rw [show cbz ((M : ℤ) + n) ((M : ℤ) + n - a)
          = cbz ((M : ℤ) + n) (a : ℤ) from by
        rw [show (M : ℤ) + n = ((M + n : ℕ) : ℤ) from by push_cast; ring,
          ← ZhuMu.cbz_symm (M + n) (a : ℤ)]]
    rw [show ((M : ℤ) + P - 2 - μ - γ - j) - ((M : ℤ) + n - a)
          = (P : ℤ) - n - 2 - μ - γ - j + a from by ring,
      show γ + (n : ℤ) + 1 - M + ((M : ℤ) + n - a) = γ + 2 * (n : ℤ) + 1 - a from by ring,
      show γ - M - n + ((M : ℤ) + n - a) = γ - a from by ring]
    ring

/-- The base-`P+n` per-`(j,kp)` kernel: `GvLn_j(kp) = ∑_t C(n+1, t)·VHkerLn_j(kp+t)`. -/
noncomputable def GvLn (M n j : ℕ) (γ : ℤ) (kp : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (n + 1 + 1), cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ (kp + t)

/-- `VHkerLn` vanishes below `n+1+j` (the `C(γ+2n+1-b, γ-b)` factor). -/
theorem VHkerLn_lo (M n j : ℕ) (γ : ℤ) {k : ℤ} (hk : k < (n : ℤ) + 1 + j) :
    VHkerLn M n j γ k = 0 := by
  rw [VHkerLn]
  rw [cbz_apply_neg (γ + 2 * (n : ℤ) + 1 - (((n : ℤ) + 1 + γ + j) - k))
    (by omega : γ - (((n : ℤ) + 1 + γ + j) - k) < 0), mul_zero]

/-- `VHkerLn` vanishes above `γ+n+1+j` (the `C(M+n, b)` factor: lower `< 0`). -/
theorem VHkerLn_hi (M n j : ℕ) (γ : ℤ) {k : ℤ} (hk : γ + (n : ℤ) + 1 + j < k) :
    VHkerLn M n j γ k = 0 := by
  rw [VHkerLn, cbz_apply_neg ((M : ℤ) + n) (by omega), zero_mul]

/-- **`VInnerILn` as a base-`P+n` finsum.** -/
theorem VInnerILn_eq_GvLnFinsum (M P n j : ℕ) (γ μ : ℤ) :
    VInnerILn M P n j γ μ
      = ∑ᶠ kp : ℤ, cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp) * GvLn M n j γ kp := by
  rw [VInnerILn_eq_VASumLn, VASumLn_eq_kFinsum]
  have hsplit : ∀ k : ℤ,
      cbz ((P : ℤ) + 2 * n + 1) (((μ : ℤ) + 2 * n + 2) + k)
        = ∑ᶠ t : ℤ, cbz ((n : ℤ) + 1) t * cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t) := by
    intro k
    rw [show (P : ℤ) + 2 * n + 1 = ((n : ℤ) + 1) + ((P : ℤ) + n) from by ring,
      ← cbz_vandermonde ((n : ℤ) + 1) ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + k), cbzConvol]
  rw [show (∑ᶠ k : ℤ, cbz ((P : ℤ) + 2 * n + 1) (((μ : ℤ) + 2 * n + 2) + k) * VHkerLn M n j γ k)
        = ∑ᶠ k : ℤ, ∑ t ∈ Finset.range (n + 1 + 1),
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k) from
      finsum_congr fun k => by
        rw [hsplit k, finsum_mul,
          finsumZ_eq_range_sum (N := n + 1 + 1)
            (fun t : ℤ => cbz ((n : ℤ) + 1) t * cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
                * VHkerLn M n j γ k)
            (fun p hp => by dsimp only; rw [cbz_apply_neg ((n : ℤ) + 1) hp, zero_mul, zero_mul])
            (fun p hp => by
              dsimp only
              rw [cbz_lt (by positivity) (by
                have : (n + 1 + 1 : ℤ) ≤ p := by exact_mod_cast hp
                omega : (n : ℤ) + 1 < p), zero_mul, zero_mul])]
        refine Finset.sum_congr rfl fun t _ => by ring]
  rw [show (∑ᶠ k : ℤ, ∑ t ∈ Finset.range (n + 1 + 1),
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k))
        = ∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ k : ℤ,
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k) from by
      rw [← sum_finsum_comm (Finset.range (n + 1 + 1))
          (fun t k => cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k))
          (fun t _ => ?_)]
      apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1 + j) (γ + (n : ℤ) + 1 + j))
      intro k hk
      rw [Function.mem_support] at hk
      rw [Set.mem_Icc]
      by_contra hcon
      apply hk
      simp only []
      rcases not_and_or.mp hcon with h | h
      · rw [VHkerLn_lo M n j γ (by omega : k < (n : ℤ) + 1 + j), mul_zero, mul_zero]
      · rw [VHkerLn_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < k), mul_zero, mul_zero]]
  rw [show (∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ k : ℤ,
            cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k))
        = ∑ t ∈ Finset.range (n + 1 + 1), ∑ᶠ kp : ℤ,
            cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
              * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ (kp + (t : ℤ))) from
      Finset.sum_congr rfl fun t _ => by
        rw [← finsum_comp_equiv (Equiv.addRight (t : ℤ))
            (f := fun k : ℤ => cbz ((P : ℤ) + n) ((((μ : ℤ) + 2 * n + 2) + k) - t)
                * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ k))]
        simp only [Equiv.coe_addRight]
        refine finsum_congr fun kp => by
          rw [show (((μ : ℤ) + 2 * n + 2) + (kp + (t : ℤ))) - t = ((μ : ℤ) + 2 * n + 2) + kp from by ring]]
  have hfin : ∀ t ∈ Finset.range (n + 1 + 1),
      Function.HasFiniteSupport (fun kp : ℤ => cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
          * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ (kp + (t : ℤ)))) := by
    intro t _
    apply Set.Finite.subset (Set.finite_Icc ((n : ℤ) + 1 + j - t) (γ + (n : ℤ) + 1 + j - t))
    intro kp hkp
    rw [Function.mem_support] at hkp
    rw [Set.mem_Icc]
    by_contra hcon
    apply hkp
    rcases not_and_or.mp hcon with h | h
    · rw [VHkerLn_lo M n j γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1 + j), mul_zero, mul_zero]
    · rw [VHkerLn_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < kp + (t : ℤ)), mul_zero, mul_zero]
  rw [sum_finsum_comm (Finset.range (n + 1 + 1))
      (fun t kp => cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp)
          * (cbz ((n : ℤ) + 1) (t : ℤ) * VHkerLn M n j γ (kp + (t : ℤ)))) hfin]
  refine finsum_congr fun kp => ?_
  rw [GvLn, Finset.mul_sum]

/-- For `γ < 0` the kernel `VHkerLn` vanishes identically. -/
theorem VHkerLn_gneg (M n j : ℕ) {γ : ℤ} (hγ : γ < 0) (k : ℤ) : VHkerLn M n j γ k = 0 := by
  rw [VHkerLn]
  rcases le_or_gt k (γ + (n : ℤ) + 1 + j) with hk | hk
  · rw [cbz_apply_neg (γ + 2 * (n : ℤ) + 1 - (((n : ℤ) + 1 + γ + j) - k))
      (by omega : γ - (((n : ℤ) + 1 + γ + j) - k) < 0), mul_zero]
  · rw [cbz_apply_neg ((M : ℤ) + n) (by omega : ((n : ℤ) + 1 + γ + j) - k < 0), zero_mul]

/-- `GvLn` vanishes for `kp < 0`. -/
theorem GvLn_lo (M n j : ℕ) (γ : ℤ) (hjn : j ≤ n) {kp : ℤ} (hkp : kp < 0) : GvLn M n j γ kp = 0 := by
  rw [GvLn]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (t : ℤ) ≤ (n : ℤ) + 1 := by
    have := Finset.mem_range.mp ht; exact_mod_cast (by omega : t ≤ n + 1)
  have hjn' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjn
  rw [VHkerLn_lo M n j γ (by omega : kp + (t : ℤ) < (n : ℤ) + 1 + j), mul_zero]

/-- `GvLn` vanishes for `2n+2+γ ≤ kp` (when `j ≤ n`). -/
theorem GvLn_hi (M n j : ℕ) (γ : ℤ) (hjn : j ≤ n) {kp : ℤ} (hkp : 2 * (n : ℤ) + 2 + γ ≤ kp) :
    GvLn M n j γ kp = 0 := by
  rw [GvLn]
  refine Finset.sum_eq_zero fun t ht => ?_
  have htle : (t : ℤ) ≤ (n : ℤ) + 1 := by
    have := Finset.mem_range.mp ht; exact_mod_cast (by omega : t ≤ n + 1)
  have hjn' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hjn
  rw [VHkerLn_hi M n j γ (by omega : γ + (n : ℤ) + 1 + j < kp + (t : ℤ)), mul_zero]

/-- The LEFT V per-`j` tower weight (`tower_swap` weight at base `P+n`). -/
noncomputable def vtJLn (M n j : ℕ) (γ : ℤ) (ν : ℕ) : ℂ :=
  ∑ kp ∈ Finset.range (2 * n + 2 + γ).toNat,
    (-1 : ℂ) ^ (kp - ν) * cbz (kp : ℤ) (ν : ℤ) * GvLn M n j γ (kp : ℤ)

/-- **Per-`j` `VInnerILn` tower collapse** (grade `P`). -/
theorem VInnerILn_tower (M P n j : ℕ) (γ μ : ℤ) (hjn : j ≤ n) :
    VInnerILn M P n j γ μ
      = ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
          vtJLn M n j γ ν * cbz ((P : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) := by
  rw [VInnerILn_eq_GvLnFinsum]
  rw [show (∑ᶠ kp : ℤ, cbz ((P : ℤ) + n) (((μ : ℤ) + 2 * n + 2) + kp) * GvLn M n j γ kp)
        = ∑ᶠ kp : ℤ, cbz (((P + n : ℕ)) : ℤ) (((μ : ℤ) + 2 * n + 2) + kp) * GvLn M n j γ kp from by
      push_cast; rfl]
  rw [tower_swap (P + n) (μ + 2 * n + 2) (GvLn M n j γ) (2 * n + 2 + γ).toNat
      (fun k hk => GvLn_lo M n j γ hjn hk)
      (fun k hk => GvLn_hi M n j γ hjn (by
        have hh : ((2 * n + 2 + γ).toNat : ℤ) ≤ k := hk
        rcases lt_or_ge (2 * (n : ℤ) + 2 + γ) 0 with h | h
        · rw [Int.toNat_of_nonpos (by omega)] at hh; omega
        · rw [Int.toNat_of_nonneg h] at hh; omega))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [vtJLn]
  congr 2

/-- **The depth-`n` LEFT V-core weights**. -/
noncomputable def wVLn (M n : ℕ) (γ : ℤ) (δ : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * vtJLn M n j γ δ

/-- **The LEFT V-core scalar collapse** (grade `P`). -/
theorem VgammaModeCollLn_eq_towerCoeff (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeCollLn M P n G γ μ
      = towerCoeff P n (wVLn M n γ) (2 * n + 2 + max γ 0).toNat μ := by
  rw [VgammaModeCollLn_eq_jSum M P n G hG γ μ, towerCoeff]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, show max γ 0 = γ from by omega]
    rw [show ∑ j ∈ Finset.range (n + 1),
              (-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * VInnerILn M P n j γ μ
          = ∑ j ∈ Finset.range (n + 1), ∑ ν ∈ Finset.range (2 * n + 2 + γ).toNat,
              ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ) * vtJLn M n j γ ν)
                * cbz ((P : ℤ) + n + ν) ((μ + 2 * n + 2) + ν) from
        Finset.sum_congr rfl fun j hj => by
          rw [VInnerILn_tower M P n j γ μ (by have := Finset.mem_range.mp hj; omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => by ring,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [wVLn, Finset.sum_mul]
  · rw [if_neg hγ, show max γ 0 = 0 from by omega]
    symm
    refine Finset.sum_eq_zero fun δ _ => ?_
    rw [show wVLn M n γ δ = 0 from ?_, zero_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show vtJLn M n j γ δ = 0 from ?_, mul_zero]
    refine Finset.sum_eq_zero fun kp _ => ?_
    rw [show GvLn M n j γ kp = 0 from ?_, mul_zero]
    rw [GvLn]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [VHkerLn_gneg M n j (by omega : γ < 0) (kp + (t : ℤ)), mul_zero]

/-! ## Step L-7 — the side collapses and the assembled `LeftCircTowerEqn` / `hLcirc_closed`.

Mirror of `ZhuVermaAnDescent21`: the per-`(γ,μ)` cores feed the side collapses
`USideLn = UfamOn`, `VSideLn = −VfamOn` over a common window/depth, then `LeftCircTowerEqn_of_sides`
+ `hLcirc_of_towerEq` (`ZhuVermaAnArchL1`) assemble the FULL field. -/

/-- `UgammaCoeffLn` vanishes below `γ = -(2n+1)` (its guard `(p-(n+j+1)) ≤ γ` fails). -/
theorem UgammaCoeffLn_zero_below (M P n : ℕ) (G : ℕ → ℕ) (i j p : ℕ) (γ : ℤ)
    (hj : j ≤ n) (hγ : γ < -(2 * (n : ℤ) + 1)) : UgammaCoeffLn M P n G i j p γ = 0 := by
  rw [UgammaCoeffLn, if_neg]
  have hp : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
  have hj' : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hj
  omega

/-- The collected LEFT U scalar `UgammaModeCollLn` vanishes for `γ < -(2n+1)`. -/
theorem UgammaModeCollLn_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ)
    (hγ : γ < -(2 * (n : ℤ) + 1)) : UgammaModeCollLn M P n G γ μ = 0 := by
  rw [UgammaModeCollLn]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
    Finset.sum_eq_zero fun p _ => ?_
  rw [UgammaCoeffLn_zero_below M P n G i j p γ (by have := Finset.mem_range.mp hj; omega) hγ]
  simp only [ite_self]

/-- The collected LEFT V scalar `VgammaModeCollLn` vanishes for `γ < 0` (the `VgammaCoeffLn` guard). -/
theorem VgammaModeCollLn_zero_below (M P n : ℕ) (G : ℕ → ℕ) (γ μ : ℤ) (hγ : γ < 0) :
    VgammaModeCollLn M P n G γ μ = 0 := by
  rw [VgammaModeCollLn]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun p _ => ?_
  rw [show VgammaCoeffLn M P n G i j p γ = 0 from by rw [VgammaCoeffLn, if_neg (by omega)],
    ite_self]

/-- The U-side double-finsum body vanishes once the base `d₍γ₎b = 0`. -/
theorem USideLn_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (G : ℕ → ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ b = 0) (γ : ℤ) (hγ : Nd ≤ γ) :
    (∑ᶠ μ : ℤ, UgammaModeCollLn M P n G γ μ • W.smul c μ (W.smul d γ b)) = 0 := by
  rw [show W.smul d γ b = (0 : 𝒱) from hNd γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- The V-side double-finsum body vanishes once the base `c₍γ₎b = 0`. -/
theorem VSideLn_gammaBody_zero_above (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (G : ℕ → ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ b = 0) (γ : ℤ) (hγ : Nc ≤ γ) :
    (∑ᶠ μ : ℤ, VgammaModeCollLn M P n G γ μ • W.smul d μ (W.smul c γ b)) = 0 := by
  rw [show W.smul c γ b = (0 : 𝒱) from hNc γ hγ]
  simp only [PreVertexAlgebra.smul_zero_right, smul_zero, finsum_zero]

/-- **U-side collapse (LEFT).** -/
theorem USideLn_eq_UfamOn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nd : ℤ} (hNd : ∀ γ : ℤ, Nd ≤ γ → W.smul d γ b = 0)
    (hγ₀ : γ₀ ≤ -(2 * (n : ℤ) + 1)) (hΓ : Nd ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → (2 * n + 2 + γ).toNat ≤ Δ) :
    USideLn W M P n c d b (Gwit M P n) = UfamOn W M n c d b (wULn P n) γ₀ Γ Δ := by
  rw [USideLn_eq_gammaModeFinsum, UfamOn_eq_finsum]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, UgammaModeCollLn M P n (Gwit M P n) γ μ • W.smul c μ (W.smul d γ b))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    refine finsum_congr fun μ => ?_
    congr 1
    rw [UgammaModeCollLn_eq_towerCoeff M P n (Gwit M P n) (Gwit_spec M P n) (γ₀ + (g : ℤ)) μ]
    rw [towerCoeff_pad M n (wULn P n (γ₀ + (g : ℤ))) (2 * n + 2 + (γ₀ + (g : ℤ))).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => ?_)]
    -- `wULn` vanishes past its depth (`cbz(k,δ)=0` for `k<δ`).
    rw [wULn]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show wtJLn P n j (γ₀ + (g : ℤ)) δ = 0 from ?_, mul_zero]
    rw [wtJLn]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < (2 * n + 2 + (γ₀ + (g : ℤ))).toNat := Finset.mem_range.mp hk
    rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : k < δ)), mul_zero, zero_mul]
  · intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [UgammaModeCollLn_zero_below M P n (Gwit M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact USideLn_gammaBody_zero_above W M P n c d b (Gwit M P n) hNd γ (by omega)

/-- **V-side collapse (LEFT).** -/
theorem VSideLn_eq_neg_VfamOn (W : VertexOperatorAlgebra 𝒱) (M P n : ℕ) (c d b : 𝒱)
    (γ₀ : ℤ) (Γ Δ : ℕ) {Nc : ℤ} (hNc : ∀ γ : ℤ, Nc ≤ γ → W.smul c γ b = 0)
    (hγ₀ : γ₀ ≤ 0) (hΓ : Nc ≤ γ₀ + Γ)
    (hΔ : ∀ γ : ℤ, γ₀ ≤ γ → γ < γ₀ + Γ → (2 * n + 2 + max γ 0).toNat ≤ Δ) :
    VSideLn W M P n c d b (Gwit M P n)
      = -VfamOn W P n c d b (fun γ => fun δ => -(wVLn M n γ δ)) γ₀ Γ Δ := by
  rw [VSideLn_eq_gammaModeFinsum, VfamOn_eq_finsum, ← Finset.sum_neg_distrib]
  rw [finsum_window
      (fun γ : ℤ => ∑ᶠ μ : ℤ, VgammaModeCollLn M P n (Gwit M P n) γ μ • W.smul d μ (W.smul c γ b))
      γ₀ Γ ?_]
  · refine Finset.sum_congr rfl fun g hg => ?_
    rw [← finsum_neg_distrib]
    refine finsum_congr fun μ => ?_
    rw [← neg_smul]
    congr 1
    rw [VgammaModeCollLn_eq_towerCoeff M P n (Gwit M P n) (Gwit_spec M P n) (γ₀ + (g : ℤ)) μ,
      towerCoeff_neg, neg_neg]
    rw [towerCoeff_pad P n (wVLn M n (γ₀ + (g : ℤ))) (2 * n + 2 + max (γ₀ + (g : ℤ)) 0).toNat Δ μ
        (hΔ (γ₀ + (g : ℤ)) (by omega) (by have := Finset.mem_range.mp hg; omega))
        (fun δ hδ => ?_)]
    -- `wVLn` vanishes past its depth.
    rw [wVLn]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show vtJLn M n j (γ₀ + (g : ℤ)) δ = 0 from ?_, mul_zero]
    rw [vtJLn]
    refine Finset.sum_eq_zero fun kp hkp => ?_
    have hkp' : kp < (2 * n + 2 + (γ₀ + (g : ℤ))).toNat := Finset.mem_range.mp hkp
    have hmono : (2 * n + 2 + (γ₀ + (g : ℤ))).toNat ≤ (2 * n + 2 + max (γ₀ + (g : ℤ)) 0).toNat := by
      apply Int.toNat_le_toNat; omega
    rw [cbz_lt (by positivity) (by exact_mod_cast (by omega : kp < δ)), mul_zero, zero_mul]
  · intro γ hγ
    refine ⟨?_, ?_⟩
    · by_contra h
      apply hγ
      refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
      rw [VgammaModeCollLn_zero_below M P n (Gwit M P n) γ μ (by omega), zero_smul]
    · by_contra h
      apply hγ
      exact VSideLn_gammaBody_zero_above W M P n c d b (Gwit M P n) hNc γ (by omega)

/-- **`LeftCircTowerEqn` for all homogeneous `c, d`** — the LEFT lift of `RightCircTowerEq_holds`. -/
theorem LeftCircTowerEqn_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (M P : ℕ) {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (b : 𝒱) :
    LeftCircTowerEqn W n M P c d b := by
  obtain ⟨Nd, hNd⟩ := W.regularity d b
  obtain ⟨Nc, hNc⟩ := W.regularity c b
  set γ₀ : ℤ := -(2 * (n : ℤ) + 1) with hγ₀
  set Γ : ℕ := (max Nd Nc - γ₀).toNat with hΓdef
  set Δ : ℕ := (2 * (n : ℤ) + 2 + max (γ₀ + (Γ : ℤ)) 0).toNat with hΔdef
  have hmaxle : max Nd Nc ≤ γ₀ + (Γ : ℤ) := by
    have := Int.self_le_toNat (max Nd Nc - γ₀)
    rw [hΓdef]; omega
  have hΓU : Nd ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_left _ _) hmaxle
  have hΓV : Nc ≤ γ₀ + (Γ : ℤ) := le_trans (le_max_right _ _) hmaxle
  refine LeftCircTowerEqn_of_sides W n hc hd b (Gwit M P n)
    (fun i _ => Gwit_spec M P n i) (wULn P n) (fun γ => fun δ => -(wVLn M n γ δ)) γ₀ Γ Δ ?_ ?_
  · refine USideLn_eq_UfamOn W M P n c d b γ₀ Γ Δ hNd (le_refl _) hΓU ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega
  · refine VSideLn_eq_neg_VfamOn W M P n c d b γ₀ Γ Δ hNc (by rw [hγ₀]; omega) hΓV ?_
    intro γ _ hub
    rw [hΔdef]
    refine Int.toNat_le_toNat ?_
    have : γ ≤ γ₀ + (Γ : ℤ) := by omega
    omega

/-- **(L1∘) closed.**  The full left-circle ideal field: for every `n`, `c, d, b`,
`leftProd W n (circ W n c d) b ∈ OnFull W n`.  Assembled from the two proven scalar cores via
`LeftCircTowerEqn_holds` and the `ZhuVermaAnArchL1` reduction `hLcirc_of_towerEq`. -/
theorem hLcirc_closed (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ c d b : 𝒱, leftProd W n (circ W n c d) b ∈ OnFull W n :=
  hLcirc_of_towerEq W n (fun M P c hc d hd b => LeftCircTowerEqn_holds W n M P hc hd b)

end VOA
