/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent15

/-!
# The `r`/guard elimination of the per-`(γ,μ)` scalar collections `UgammaModeColl`/`VgammaModeColl`.

This file targets the two scalar tower-collapse cores that feed `RightCircTowerEq_of_collapse`
(`ZhuVermaAnDescent10`): the per-`(γ,μ)` U/V collected scalars `UgammaModeColl`/`VgammaModeColl`
should each collapse onto a finite `PresOn`-tower coefficient `towerCoeff M n (wU γ) Δ μ` (grade `M`,
U-side) resp. `towerCoeff P n (wV γ) Δ μ` (grade `P`, V-side), with the (Mathematica-verified)
uniform tower depth `Δ = 2n+2 + max(γ-γ₀, 0)`, `γ₀ = -(2n+1)` (U) / `0` (V).

## The genuine first reduction step proved here: `r`/guard elimination

`UgammaModeColl M P n G γ μ` (`ZhuVermaAnDescent10`) is the finite `(i,j,r)`-sum, with the *mode
indicator* `μ = (i-2n-2)+(r-(n+j+1))-γ`, of the `mode_iterate` coefficient `UgammaCoeff`.  The
indicator solves for the FZ residue index `r` UNIQUELY in terms of `(i,j,γ,μ)`:

  `r = μ + γ + 3n+3 + j - i`   (call this `r₀ i j`, an integer),

and the per-`(i,j)` inner `r`-sum collapses onto that single value, AFTER which the `mode_iterate`
peeling index degenerates to `s = (i-2n-2) - μ` (a `ℕ` via `.toNat`), with the U/V guards
(`UgammaCoeff`'s `N ≤ γ` ⇔ `0 ≤ s`, and the `assemblyLead` inner-grade `if`) absorbed into the
generalized binomials `gBinom`/`cbz` (which vanish off-support).  This eliminates the `r`-finset and
the `mode_iterate` guard, leaving the **direct `(i,j)`-double-sum scalar**

  `UgammaModeColl M P n G γ μ`
    `= ∑_{i≤M+n} ∑_{j≤n} cbz(M+n,i)·(-1)^j cbz(j+n,j)·(if 0≤G_iℤ then cbz(G_iℤ+j, r₀ i j) else 0)`
          `· (-1)^s · gBinom(i-2n-2, s)`,   `s = ((i-2n-2)-μ).toNat`,
  `VgammaModeColl M P n G γ μ`
    `= ∑_{i≤M+n} ∑_{j≤n} cbz(M+n,i)·(-1)^j cbz(j+n,j)·(if 0≤G_iℤ then cbz(G_iℤ+j, r₀ i j) else 0)`
          `· (-1)^γ · gBinom(i-2n-2, γ.toNat) · (-1)^(i-2n-2)`,

with `r₀ i j = μ + γ + 3n+3 + j - i` and `G_iℤ = M+P-(i-2n-2)-1`.

This is EXACTLY the index frame the depth-`n` engine `ZhuRes.gen_vandermonde` (per FZ index `j`, on
the inner `i`-sum) + `ZhuRes.gen_jsum` (the FZ `j`-sum) consumes — the same frame as the
commutator-family core `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`), but with the `mode_iterate`
base-mode `γ` / mode `μ` reindexing (`UgammaCoeff`/`VgammaCoeff`) in place of the commutator
reindexing `inner_reindexN`.  Mathematica (exact `Solve`, `n = 1,2`, `M,P ≤ 2`, all
contributing base modes `γ`) confirms both direct-form scalars equal a `towerCoeff M n (wU γ) Δ μ`
resp. `towerCoeff P n (wV γ) Δ μ` with the stated `Δ`.

## Status proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `directUCoeff` / `directVCoeff` — the per-`(i,j)` direct (`r`-substituted, guard-free) scalars;
* **`UgammaModeColl_eq_directSum`** / **`VgammaModeColl_eq_directSum`** — the `r`/guard elimination:
  the indicator `r`-finset-sum collapses onto the single substituted `r₀` (the `cbz` upper index
  vanishing off the residue support absorbs both the finset bound and the `mode_iterate` guard);
* **`gBinom_upper_neg`** + **`uIter_eq_cbz`** / **`vIter_core`** — the upper-negation reflection
  turning the guarded `gBinom` peeling factor into a single integer binomial `cbz`;
* `directUCoeff'` / `directVCoeff'` + **`UgammaModeColl_eq_directSum'`** / **`VgammaModeColl_eq_directSum'`**
  — the collected scalars in the engine-ready `cbz`-only "Vandermonde frame".

## What remains (the PRECISE depth-`n` tower-collapse target — NOT `sorry`, NOT axiomatized)

The remaining content of each scalar core is the depth-`n` collapse of the proved direct
`(i,j)`-double-sum onto the `towerCoeff` form — the depth-`n` lift of `coeffSn_eq_coeffPn`
(`gen_vandermonde` per `j` on the inner `i`-sum, then `gen_jsum` on the FZ `j`-sum), in the
`mode_iterate` reindexing frame.  The one genuine new ingredient versus `coeffSn_eq_coeffPn` is the
`i`-dependent inner residue grade `G_iℤ = M+P-(i-2n-2)-1` appearing in `cbz(G_iℤ+j, r₀ i j)` (the
"`i`-dependent grade Vandermonde"); the existence of the tower weights `wU γ`/`wV γ` (not
their closed form) is Mathematica-verified for `n = 1,2`.  The PRECISE remaining targets:

  **(U-core)** `∀ wU?, UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ`  (grade `M`),
  **(V-core)** `∀ wV?, VgammaModeColl M P n G γ μ = towerCoeff P n (wV γ) Δ μ`  (grade `P`),

with `Δ = 2n+2 + max(γ-γ₀,0)`.  Supplying these (over the proved direct forms) feeds
`RightCircTowerEq_of_collapse` (`ZhuVermaAnDescent10`) the `HU`/`HV` scalar matchings and discharges
`RightCircTowerEq_holds` outright.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The substituted residue index and the direct (`r`-eliminated, guard-free) U/V scalars. -/

/-- The unique FZ residue index `r` solving the U/V mode indicator
`μ = (i-2n-2)+(r-(n+j+1))-γ`, as an integer: `r₀ = μ + γ + 3n+3 + j - i`. -/
def rSub (n : ℕ) (i j : ℕ) (γ μ : ℤ) : ℤ :=
  μ + γ + 3 * (n : ℤ) + 3 + (j : ℤ) - (i : ℤ)

/-- The per-`(i,j)` direct U-side scalar: `UgammaCoeff` with `r` substituted by `rSub`.  The
`mode_iterate` guard `N ≤ γ` of `UgammaCoeff` becomes the residue guard `μ ≤ (i-2n-2)` (so the
peeling index `s = (i-2n-2)-μ ≥ 0`); off that guard the term vanishes, hence the inner `if`. -/
noncomputable def directUCoeff (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
    * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        then cbz ((G i : ℤ) + j) (rSub n i j γ μ) else 0)
    * (if μ ≤ (i : ℤ) - 2 * (n : ℤ) - 2
        then (-1 : ℂ) ^ (((i : ℤ) - 2 * (n : ℤ) - 2) - μ).toNat
              * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ).toNat
        else 0)

/-- The per-`(i,j)` direct V-side scalar: `VgammaCoeff` with `r` substituted by `rSub`.  The
`mode_iterate` peeling index is the base-mode `γ` itself (`γ.toNat`), with the V-sign
`(-1)^(i-2n-2)`; the `VgammaCoeff` guard `0 ≤ γ` is the (`(i,j)`-independent) outer `if`. -/
noncomputable def directVCoeff (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
      * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
          then cbz ((G i : ℤ) + j) (rSub n i j γ μ) else 0)
      * ((-1 : ℂ) ^ γ.toNat * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat)
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-! ## The per-`(i,j)` inner `r`-finset collapse onto the substituted index. -/

/-- For a nonnegative integer upper index `A : ℤ`, `cbz A r₀` vanishes off the residue support
`[0, A]`.  Used to absorb the per-`(i,j)` finset bound `[0, G_i+n]`: any out-of-finset substituted
index `r₀` lands beyond `A = G_iℤ+j ≤ G_iℤ+n` (`j ≤ n`), so `cbz A r₀ = 0`. -/
theorem cbz_zero_off_range {A r₀ : ℤ} (hA : 0 ≤ A) (hr : r₀ < 0 ∨ A < r₀) : cbz A r₀ = 0 := by
  rcases hr with hlt | hgt
  · exact cbz_apply_neg A hlt
  · exact cbz_lt hA hgt

/-- **Matched-term identity (U-side).**  When the substituted index `(r : ℤ) = rSub n i j γ μ`
(equivalently the mode indicator `μ = (i-2n-2)+(r-(n+j+1))-γ` holds), the `mode_iterate` coefficient
`UgammaCoeff M P n G i j r γ` equals the direct scalar `directUCoeff M P n G i j γ μ`.  The guard
`(r-(n+j+1)) ≤ γ` becomes `μ ≤ (i-2n-2)`, and the peeling index `(γ-(r-(n+j+1))).toNat` becomes
`((i-2n-2)-μ).toNat`. -/
theorem UgammaCoeff_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ μ : ℤ)
    (hr : (r : ℤ) = rSub n i j γ μ) :
    UgammaCoeff M P n G i j r γ = directUCoeff M P n G i j γ μ := by
  -- `r - (n+j+1) = γ + (μ - (i-2n-2))`, so `γ - (r-(n+j+1)) = (i-2n-2) - μ`.
  have hN : (r : ℤ) - ((n : ℤ) + (j : ℤ) + 1) = γ + (μ - ((i : ℤ) - 2 * (n : ℤ) - 2)) := by
    rw [hr, rSub]; ring
  have hdiff : γ - ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) = ((i : ℤ) - 2 * (n : ℤ) - 2) - μ := by
    rw [hN]; ring
  rw [UgammaCoeff, directUCoeff]
  by_cases hguard : (r : ℤ) - ((n : ℤ) + (j : ℤ) + 1) ≤ γ
  · -- guard holds ⇔ `μ ≤ (i-2n-2)`.
    rw [if_pos hguard]
    have hmu : μ ≤ (i : ℤ) - 2 * (n : ℤ) - 2 := by rw [hN] at hguard; omega
    rw [if_pos hmu, assemblyLead]
    -- both sides: `(cbz(M+n,i)·sgnⱼ·[if grade then cbz(G_i+j, r) else 0])·((-1)^s gBinom ℓ s)`.
    rw [hdiff]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, if_pos hgr, show (r : ℤ) = rSub n i j γ μ from hr]
    · rw [if_neg hgr, if_neg hgr]; ring
  · -- guard fails ⇔ `μ > (i-2n-2)`.
    rw [if_neg hguard]
    have hmu : ¬ μ ≤ (i : ℤ) - 2 * (n : ℤ) - 2 := by rw [hN] at hguard; omega
    rw [if_neg hmu, mul_zero]

/-- **Matched-term identity (V-side).**  When `(r : ℤ) = rSub n i j γ μ`, the `mode_iterate`
coefficient `VgammaCoeff M P n G i j r γ` equals the direct scalar `directVCoeff M P n G i j γ μ`. -/
theorem VgammaCoeff_at_rSub (M P n : ℕ) (G : ℕ → ℕ) (i j r : ℕ) (γ μ : ℤ)
    (hr : (r : ℤ) = rSub n i j γ μ) :
    VgammaCoeff M P n G i j r γ = directVCoeff M P n G i j γ μ := by
  rw [VgammaCoeff, directVCoeff]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ, assemblyLead]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, if_pos hgr, show (r : ℤ) = rSub n i j γ μ from hr]
    · rw [if_neg hgr, if_neg hgr]; ring
  · rw [if_neg hγ, if_neg hγ]

/-! ## The per-`(i,j)` inner `r`-finset collapse. -/

/-- **Inner `r`-finset collapse (U-side).**  The per-`(i,j)` indicator `r`-finset-sum of
`UgammaCoeff` (over `r ∈ [0, G_i+n]`, indicator `μ = (i-2n-2)+(r-(n+j+1))-γ`) collapses to the
single direct scalar `directUCoeff M P n G i j γ μ`.  The unique matching index is `r = rSub`; when
`rSub` lands outside `[0, G_i+n]` the finset has no matching term AND `cbz(G_iℤ+j, rSub) = 0`
(`cbz_zero_off_range`, since `G_iℤ+j ≤ G_iℤ+n` as `j ≤ n`), so both sides vanish. -/
theorem Uinner_collapse (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (hj : j ≤ n) :
    (∑ r ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then UgammaCoeff M P n G i j r γ else 0))
      = directUCoeff M P n G i j γ μ := by
  -- the indicator condition is `(r : ℤ) = rSub n i j γ μ`.
  have hcond : ∀ r : ℕ,
      (μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
        ↔ ((r : ℤ) = rSub n i j γ μ) := by
    intro r; rw [rSub]; constructor <;> intro h <;> omega
  have hrw : (∑ r ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then UgammaCoeff M P n G i j r γ else 0))
      = ∑ r ∈ Finset.range (G i + n + 1),
        (if (r : ℤ) = rSub n i j γ μ then UgammaCoeff M P n G i j r γ else 0) :=
    Finset.sum_congr rfl fun r _ => by simp only [hcond r]
  rw [hrw]
  by_cases hpos : 0 ≤ rSub n i j γ μ
  · -- the matching natural index is `r₀ := (rSub).toNat`.
    set r₀ : ℕ := (rSub n i j γ μ).toNat with hr₀
    have hr₀cast : (r₀ : ℤ) = rSub n i j γ μ := by rw [hr₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : r₀ ∈ Finset.range (G i + n + 1)
    · -- the finset contains `r₀`: collapse to its term, then `UgammaCoeff_at_rSub`.
      rw [Finset.sum_eq_single_of_mem r₀ hmem
        (fun r _ hne => by
          rw [if_neg (by
            intro hc
            exact hne (by
              have : (r : ℤ) = (r₀ : ℤ) := by rw [hr₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hr₀cast, UgammaCoeff_at_rSub M P n G i j r₀ γ μ hr₀cast]
    · -- `r₀ ∉ range`, i.e. `rSub > G_i + n`: no matching term, and `cbz(G_iℤ+j, rSub) = 0`.
      have hgt : (G i : ℤ) + n < rSub n i j γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + n + 1 ≤ r₀ := by omega
        have hle : ((G i + n + 1 : ℕ) : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast this
        rw [hr₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun r hr => by
        rw [if_neg (by
          rw [Finset.mem_range] at hr
          intro hc
          have hrle : r ≤ G i + n := by omega
          have hle : (r : ℤ) ≤ (G i : ℤ) + n := by exact_mod_cast hrle
          rw [hc] at hle; omega)]]
      -- RHS `directUCoeff` vanishes: `cbz(G_iℤ+j, rSub) = 0`.
      rw [directUCoeff]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
      · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ) + j) (by rw [hG hgr]; omega)
          (Or.inr (by
            have hjn : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hj
            omega))]
        ring
      · rw [if_neg hgr]; ring
  · -- `rSub < 0`: no nonnegative `r` matches, and `cbz(G_iℤ+j, rSub) = 0` (lower index `< 0`).
    replace hpos : rSub n i j γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun r _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
        rw [hc] at this; omega)]]
    rw [directUCoeff]
    by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
    · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ) + j) (by omega)]; ring
    · rw [if_neg hgr]; ring

/-- **Inner `r`-finset collapse (V-side).**  The V mirror of `Uinner_collapse`: the per-`(i,j)`
indicator `r`-finset-sum of `VgammaCoeff` collapses to the single direct scalar
`directVCoeff M P n G i j γ μ` (unique match `r = rSub`; off-range terms vanish via
`cbz_zero_off_range`). -/
theorem Vinner_collapse (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ)
    (hG : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (hj : j ≤ n) :
    (∑ r ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then VgammaCoeff M P n G i j r γ else 0))
      = directVCoeff M P n G i j γ μ := by
  have hcond : ∀ r : ℕ,
      (μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ)
        ↔ ((r : ℤ) = rSub n i j γ μ) := by
    intro r; rw [rSub]; constructor <;> intro h <;> omega
  have hrw : (∑ r ∈ Finset.range (G i + n + 1),
        (if μ = ((i : ℤ) - 2 * (n : ℤ) - 2) + ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) - γ
          then VgammaCoeff M P n G i j r γ else 0))
      = ∑ r ∈ Finset.range (G i + n + 1),
        (if (r : ℤ) = rSub n i j γ μ then VgammaCoeff M P n G i j r γ else 0) :=
    Finset.sum_congr rfl fun r _ => by simp only [hcond r]
  rw [hrw]
  by_cases hpos : 0 ≤ rSub n i j γ μ
  · set r₀ : ℕ := (rSub n i j γ μ).toNat with hr₀
    have hr₀cast : (r₀ : ℤ) = rSub n i j γ μ := by rw [hr₀, Int.toNat_of_nonneg hpos]
    by_cases hmem : r₀ ∈ Finset.range (G i + n + 1)
    · rw [Finset.sum_eq_single_of_mem r₀ hmem
        (fun r _ hne => by
          rw [if_neg (by
            intro hc
            exact hne (by
              have : (r : ℤ) = (r₀ : ℤ) := by rw [hr₀cast, hc]
              exact_mod_cast this))])]
      rw [if_pos hr₀cast, VgammaCoeff_at_rSub M P n G i j r₀ γ μ hr₀cast]
    · have hgt : (G i : ℤ) + n < rSub n i j γ μ := by
        rw [Finset.mem_range] at hmem
        have : G i + n + 1 ≤ r₀ := by omega
        have hle : ((G i + n + 1 : ℕ) : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast this
        rw [hr₀cast] at hle; push_cast at hle; omega
      rw [Finset.sum_eq_zero fun r hr => by
        rw [if_neg (by
          rw [Finset.mem_range] at hr
          intro hc
          have hrle : r ≤ G i + n := by omega
          have hle : (r : ℤ) ≤ (G i : ℤ) + n := by exact_mod_cast hrle
          rw [hc] at hle; omega)]]
      rw [directVCoeff]
      by_cases hγ : 0 ≤ γ
      · rw [if_pos hγ]
        by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        · rw [if_pos hgr, cbz_zero_off_range (A := (G i : ℤ) + j) (by rw [hG hgr]; omega)
            (Or.inr (by
              have hjn : (j : ℤ) ≤ (n : ℤ) := by exact_mod_cast hj
              omega))]
          ring
        · rw [if_neg hgr]; ring
      · rw [if_neg hγ]
  · replace hpos : rSub n i j γ μ < 0 := not_le.mp hpos
    rw [Finset.sum_eq_zero fun r _ => by
      rw [if_neg (by
        intro hc
        have : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
        rw [hc] at this; omega)]]
    rw [directVCoeff]
    by_cases hγ : 0 ≤ γ
    · rw [if_pos hγ]
      by_cases hgr : 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
      · rw [if_pos hgr, cbz_apply_neg ((G i : ℤ) + j) (by omega)]; ring
      · rw [if_neg hgr]; ring
    · rw [if_neg hγ]

/-! ## The `r`/guard-eliminated direct double-sum forms of the collected scalars. -/

/-- **`UgammaModeColl` as the direct `(i,j)`-double sum** (`r`/guard eliminated).  Applying the
per-`(i,j)` inner `r`-finset collapse `Uinner_collapse` (under the grade witness `hG` matching the
inner circle grades) inside the `(i,j)`-sums of `UgammaModeColl`: the indicator `r`-sum collapses
onto the single substituted index `r₀ = rSub`, leaving the guard-free `directUCoeff`.  This is the
exact index frame the depth-`n` engine `gen_vandermonde`/`gen_jsum` consumes. -/
theorem UgammaModeColl_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directUCoeff M P n G i j γ μ := by
  rw [UgammaModeColl]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact Uinner_collapse M P n G i j γ μ (hG i) (by have := Finset.mem_range.mp hj; omega)

/-- **`VgammaModeColl` as the direct `(i,j)`-double sum** (`r`/guard eliminated).  The V mirror of
`UgammaModeColl_eq_directSum`, via `Vinner_collapse`. -/
theorem VgammaModeColl_eq_directSum (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directVCoeff M P n G i j γ μ := by
  rw [VgammaModeColl]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact Vinner_collapse M P n G i j γ μ (hG i) (by have := Finset.mem_range.mp hj; omega)

/-! ## The `gBinom`/guard → single-`cbz` reflection (the "Vandermonde frame").

The `directUCoeff`/`directVCoeff` carry the `mode_iterate` peeling factor as a *guarded generalized
binomial* `gBinom` (U: `(-1)^s gBinom(ℓ,s)`, `s = (ℓ-μ).toNat`, guard `μ ≤ ℓ`; V: `(-1)^γ
gBinom(ℓ,γ.toNat)` with a separate `(-1)^ℓ` sign).  The depth-`n` engine
`ZhuRes.gen_vandermonde`/`gen_jsum` consumes a sum of *plain integer binomials* `cbz` linear in the
summation index `i`.  The upper-negation `C(X,t) = (-1)^t·C(t-1-X, t)` (`gBinom_upper_neg`)
eliminates BOTH the `gBinom` and the guard, rewriting each peeling factor as a single `cbz` (whose
off-support vanishing reproduces the dropped guard):

  **(U)** `(if μ ≤ ℓ then (-1)^s gBinom(ℓ,s) else 0) = cbz(-μ-1, ℓ-μ)`  (`uIter_eq_cbz`),
  **(V)** `(-1)^t gBinom(ℓ,t) = cbz(t-1-ℓ, t)`  (`vIter_core`, sign-stripped core).

Mathematica-verified exact (`M,P ≤ 2`, `n ≤ 2`, all `i,j`, wide `γ,μ`).  This puts both
collected scalars into the clean `cbz`-only triple-product `i`-frame the engine consumes. -/

/-- **Upper-negation for the generalized binomial.**  `C(X, t) = (-1)^t · C(t-1-X, t)` for any
integer top `X` and `t : ℕ` (Gannon 5.1.4; the classical upper-negation).  Proved by clearing the
factorial (`gBinom_mul_factorial`) and reflecting the falling product `∏_{i<t}(X-i)` via
`Finset.prod_range_reflect`. -/
theorem gBinom_upper_neg (X : ℤ) (t : ℕ) :
    gBinom X t = (-1 : ℂ) ^ t * gBinom ((t : ℤ) - 1 - X) t := by
  have hfac : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  refine mul_left_cancel₀ hfac ?_
  rw [gBinom_mul_factorial X t]
  rw [show (t.factorial : ℂ) * ((-1 : ℂ) ^ t * gBinom ((t : ℤ) - 1 - X) t)
        = (-1 : ℂ) ^ t * ((t.factorial : ℂ) * gBinom ((t : ℤ) - 1 - X) t) from by ring,
    gBinom_mul_factorial ((t : ℤ) - 1 - X) t]
  rw [← Finset.prod_range_reflect (fun i => (((t : ℤ) - 1 - X : ℤ) : ℂ) - (i : ℂ)) t]
  have hprod : (∏ k ∈ Finset.range t, ((((t : ℤ) - 1 - X : ℤ) : ℂ) - ((t - 1 - k : ℕ) : ℂ)))
      = ∏ k ∈ Finset.range t, (-1 : ℂ) * ((X : ℂ) - (k : ℂ)) :=
    Finset.prod_congr rfl fun k hk => by
      have hk' : k < t := Finset.mem_range.mp hk
      rw [show ((t - 1 - k : ℕ) : ℂ) = (t : ℂ) - 1 - (k : ℂ) from by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
      push_cast; ring
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← mul_assoc,
    ← pow_add, show t + t = 2 * t from by ring, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]

/-- **U-side peeling reflection.**  The guarded U `mode_iterate` factor `(-1)^s gBinom(ℓ,s)`
(`s = (ℓ-μ).toNat`, guard `μ ≤ ℓ`) equals the single integer binomial `cbz (-μ-1) (ℓ-μ)` (no guard:
`cbz` vanishes for the negative lower index `ℓ-μ < 0`, reproducing the dropped guard). -/
theorem uIter_eq_cbz (ℓ μ : ℤ) :
    (if μ ≤ ℓ then (-1 : ℂ) ^ (ℓ - μ).toNat * gBinom ℓ (ℓ - μ).toNat else 0)
      = cbz (-μ - 1) (ℓ - μ) := by
  by_cases h : μ ≤ ℓ
  · rw [if_pos h, cbz_apply_nonneg (-μ - 1) (by omega : 0 ≤ ℓ - μ)]
    set s : ℕ := (ℓ - μ).toNat with hs
    have hsℓ : (s : ℤ) = ℓ - μ := Int.toNat_of_nonneg (by omega)
    rw [gBinom_upper_neg ℓ s, ← mul_assoc, ← pow_add, show s + s = 2 * s from by ring, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul]
    congr 1
    omega
  · rw [if_neg h, cbz_apply_neg (-μ - 1) (by omega : ℓ - μ < 0)]

/-- **V-side peeling reflection (sign-stripped core).**  `(-1)^t · C(ℓ, t) = C(t-1-ℓ, t)` for
`ℓ : ℤ`, `t : ℕ` (`gBinom_upper_neg` read backwards) — converts the V `gBinom` factor to a single
`cbz` linear in `i` (`ℓ = i-2n-2`), the `(-1)^ℓ` V-sign retained separately. -/
theorem vIter_core (ℓ : ℤ) (t : ℕ) :
    (-1 : ℂ) ^ t * gBinom ℓ t = cbz ((t : ℤ) - 1 - ℓ) (t : ℤ) := by
  rw [cbz_apply_nonneg ((t : ℤ) - 1 - ℓ) (by positivity), Int.toNat_natCast,
    gBinom_upper_neg ℓ t, ← mul_assoc, ← pow_add, show t + t = 2 * t from by ring, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]

/-! ## The reflection-rewritten direct scalars and collected sums (the engine-ready frame). -/

/-- The reflection-rewritten U direct scalar: `directUCoeff` with the guarded `gBinom` peeling factor
replaced by the single integer binomial `cbz (-μ-1) (ℓ-μ)` (`uIter_eq_cbz`), `ℓ = i-2n-2`.  All four
factors are plain `cbz`'s; the `i`-dependence is concentrated as `cbz(M+n, i)`, the inner
residue `cbz((M+P-ℓ-1)+j, r₀)` (the `i`-dependent grade), and `cbz(-μ-1, ℓ-μ)`. -/
noncomputable def directUCoeff' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
    * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
        then cbz ((G i : ℤ) + j) (rSub n i j γ μ) else 0)
    * cbz (-μ - 1) (((i : ℤ) - 2 * (n : ℤ) - 2) - μ)

/-- `directUCoeff = directUCoeff'` (the U peeling reflection `uIter_eq_cbz`). -/
theorem directUCoeff_eq' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) :
    directUCoeff M P n G i j γ μ = directUCoeff' M P n G i j γ μ := by
  rw [directUCoeff, directUCoeff', uIter_eq_cbz ((i : ℤ) - 2 * (n : ℤ) - 2) μ]

/-- The reflection-rewritten V direct scalar: `directVCoeff` with the `gBinom` peeling factor replaced
by `cbz (γ+2n+1-i) γ` (`vIter_core`), the V-sign `(-1)^ℓ` (`ℓ = i-2n-2`) retained. -/
noncomputable def directVCoeff' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) : ℂ :=
  if 0 ≤ γ then
    cbz ((M : ℤ) + n) (i : ℤ) * ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ))
      * (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1
          then cbz ((G i : ℤ) + j) (rSub n i j γ μ) else 0)
      * cbz (γ + 2 * (n : ℤ) + 1 - (i : ℤ)) γ
      * ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
  else 0

/-- `directVCoeff = directVCoeff'` (the V peeling reflection `vIter_core`, `γ.toNat = γ` under
`0 ≤ γ`). -/
theorem directVCoeff_eq' (M P n : ℕ) (G : ℕ → ℕ) (i j : ℕ) (γ μ : ℤ) :
    directVCoeff M P n G i j γ μ = directVCoeff' M P n G i j γ μ := by
  rw [directVCoeff, directVCoeff']
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ, vIter_core ((i : ℤ) - 2 * (n : ℤ) - 2) γ.toNat]
    have hγn : (γ.toNat : ℤ) = γ := Int.toNat_of_nonneg hγ
    rw [show ((γ.toNat : ℤ) - 1 - ((i : ℤ) - 2 * (n : ℤ) - 2))
          = γ + 2 * (n : ℤ) + 1 - (i : ℤ) from by rw [hγn]; ring,
      show ((γ.toNat : ℤ)) = γ from hγn]
  · rw [if_neg hγ, if_neg hγ]

/-- **`UgammaModeColl` in the reflection-rewritten Vandermonde frame.**  Composing
`UgammaModeColl_eq_directSum` with the per-`(i,j)` peeling reflection `directUCoeff_eq'`: the
collected U scalar is the `(i,j)`-double sum of `directUCoeff'`, all factors plain `cbz`'s, ready for
`ZhuRes.gen_vandermonde` (per FZ index `j`, inner `i`-sum) + `ZhuRes.gen_jsum` (FZ `j`-sum). -/
theorem UgammaModeColl_eq_directSum' (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    UgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directUCoeff' M P n G i j γ μ := by
  rw [UgammaModeColl_eq_directSum M P n G hG γ μ]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => directUCoeff_eq' M P n G i j γ μ

/-- **`VgammaModeColl` in the reflection-rewritten Vandermonde frame** (V mirror of
`UgammaModeColl_eq_directSum'`, via `directVCoeff_eq'`). -/
theorem VgammaModeColl_eq_directSum' (M P n : ℕ) (G : ℕ → ℕ)
    (hG : ∀ i : ℕ, 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1)
    (γ μ : ℤ) :
    VgammaModeColl M P n G γ μ
      = ∑ i ∈ Finset.range (M + n + 1), ∑ j ∈ Finset.range (n + 1),
          directVCoeff' M P n G i j γ μ := by
  rw [VgammaModeColl_eq_directSum M P n G hG γ μ]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => directVCoeff_eq' M P n G i j γ μ

/-!
## What this proves and the PRECISE remaining tower-collapse target (NOT `sorry`)

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

* `rSub`, `directUCoeff`, `directVCoeff` — the substituted residue index and the per-`(i,j)` direct
  (`r`-eliminated, guard-absorbed) U/V scalars.
* `cbz_zero_off_range` — the `cbz` off-support vanishing absorbing the per-`(i,j)` finset bound.
* **`UgammaCoeff_at_rSub` / `VgammaCoeff_at_rSub`** — the matched-term identities: at the unique
  indicator solution `(r:ℤ) = rSub`, the `mode_iterate` coefficient equals the direct scalar.
* **`Uinner_collapse` / `Vinner_collapse`** — the per-`(i,j)` inner `r`-finset collapse onto the
  single substituted index (off-range terms vanish on both sides).
* **`UgammaModeColl_eq_directSum` / `VgammaModeColl_eq_directSum`** — the `r`/guard elimination:
  the collected scalars `UgammaModeColl`/`VgammaModeColl` equal the direct `(i,j)`-double sums of
  `directUCoeff`/`directVCoeff`.
* **`gBinom_upper_neg`** — the classical upper-negation `C(X,t) = (-1)^t·C(t-1-X, t)` (any integer
  top `X`, `t : ℕ`), via `gBinom_mul_factorial` + `Finset.prod_range_reflect`.
* **`uIter_eq_cbz` / `vIter_core`** — the U/V peeling reflections: the guarded `gBinom` peeling
  factor of `directUCoeff`/`directVCoeff` rewrites as a single integer binomial `cbz` (U:
  `cbz(-μ-1, ℓ-μ)`, fully unguarded; V: `cbz(γ+2n+1-i, γ)` with the `(-1)^ℓ` sign retained),
  `ℓ = i-2n-2`.  Mathematica-verified exact (`M,P ≤ 2`, `n ≤ 2`, all `i,j`, wide `γ,μ`).
* `directUCoeff'` / `directVCoeff'` + **`directUCoeff_eq'` / `directVCoeff_eq'`** — the
  reflection-rewritten per-`(i,j)` direct scalars (all factors plain `cbz`'s) equal the originals.
* **`UgammaModeColl_eq_directSum'` / `VgammaModeColl_eq_directSum'`** — the collected scalars in the
  engine-ready, `cbz`-only Vandermonde frame `∑_{i,j} directUCoeff'` / `∑_{i,j} directVCoeff'`.

These discharge the FIRST TWO reduction steps the two scalar cores require — moving the collected
`UgammaModeColl`/`VgammaModeColl` into the explicit, guard-free `(i,j)`-double-sum index frame, AND
eliminating the `gBinom`/guard apparatus so every factor is a plain integer binomial `cbz` linear in
the summation index `i` — the exact frame the depth-`n` engine `ZhuRes.gen_vandermonde`/`gen_jsum`
consumes.

PRECISE remaining target for the two scalar cores (Mathematica-verified true, exact `Solve`,
`n = 1,2`, `M,P ≤ 2`, all contributing base modes `γ`; the per-depth tower weights `wU γ`/`wV γ` are
fully determined — verified here — but need NOT be in closed form, only their existence):

  **(U-core)**  `UgammaModeColl M P n G γ μ = towerCoeff M n (wU γ) Δ μ`,  grade `M`,
  **(V-core)**  `VgammaModeColl M P n G γ μ = towerCoeff P n (wV γ) Δ μ`,  grade `P`,

with `Δ = 2n+2 + max(γ-γ₀, 0)`, `γ₀ = -(2n+1)` (U) / `0` (V).  Over the engine-ready forms
`UgammaModeColl_eq_directSum'`/`VgammaModeColl_eq_directSum'`, the irreducible content is the depth-`n`
collapse of the `directUCoeff'`/`directVCoeff'` `(i,j)`-double sum onto the `towerCoeff` form.  After
the reflection the `i`-sum is the triple `cbz`-product

  `∑_i cbz(M+n, i) · cbz((M+P+2n+1+j) - i, (μ+γ+3n+3+j) - i) · cbz(-μ-1, i - (2n+2+μ))`  (U),

whose middle factor `cbz(A-i, B-i)` (a *diagonal-shift* binomial: BOTH indices fall with `i`, with
the `i`-independent slack `A-B = M+P-n-2-μ-γ`) is the genuine new ingredient versus
`coeffSn_eq_coeffPn` — the "`i`-dependent grade Vandermonde".  The naive `cbz` symmetry
`cbz(A-i, B-i) = cbz(A-i, A-B)` FAILS for the negative-top circle indices (Mathematica-checked), so this is NOT a mechanical lift of `coeffSn_eq_coeffPn`; the genuine `i`-sum collapse to
the dual-Hahn `ν`-tower (a generalized Vandermonde with two `i`-coupled binomials) is the precise
combinatorial identity (`gen_vandermonde` per FZ index `j` on the inner `i`-sum, then `gen_jsum` on
the FZ `j`-sum, in the diagonal-shift frame) that completes the two cores.  Supplying (U-core)/(V-core)
feeds `RightCircTowerEq_of_collapse` (`ZhuVermaAnDescent10`) its `HU`/`HV` scalar matchings (per
contributing `γ`, via `UfamOn_eq_finsum`/`VfamOn_eq_finsum`) and discharges `RightCircTowerEq_holds`
outright.  Nothing here is `sorry`'d or axiomatized.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.cbz_zero_off_range
  #print axioms VOA.UgammaCoeff_at_rSub
  #print axioms VOA.VgammaCoeff_at_rSub
  #print axioms VOA.Uinner_collapse
  #print axioms VOA.Vinner_collapse
  #print axioms VOA.UgammaModeColl_eq_directSum
  #print axioms VOA.VgammaModeColl_eq_directSum
  #print axioms VOA.gBinom_upper_neg
  #print axioms VOA.uIter_eq_cbz
  #print axioms VOA.vIter_core
  #print axioms VOA.directUCoeff_eq'
  #print axioms VOA.directVCoeff_eq'
  #print axioms VOA.UgammaModeColl_eq_directSum'
  #print axioms VOA.VgammaModeColl_eq_directSum'
-/
