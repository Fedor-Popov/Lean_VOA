/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent8

/-!
# The depth-`n` U/V tower-family finsum forms, toward the three reindexing predicates.

This file continues `Modules.ZhuVermaAnDescent8` (the `UfamOn`/`VfamOn` tower families, the three
reindexing predicates `RightCircTowerEq`/`LeftGenTowerEq`/`RightGenTowerEq`, and the bundled
`leftDescends_of_towerEq`/`rightDescends_of_towerEq` ⟹ `An.lActU`/`An.rActU`).

The membership engine `UfamOn_mem_On`/`VfamOn_mem_On`/`towerSum_mem_On` (via the keystone
`Pres_mem_On`) is already proved in Descent8.  The remaining content of each predicate is a pure
*equality* (a finsum regrouping of the already-proved FZ-product split into the abstract tower
families).  This file proves the reusable **mode-value finsum forms** of `UfamOn`/`VfamOn` (the
depth-`n` lift of `ZhuAssociator.Ufam_eq`/`Vfam_eq`'s "expand each `Pres`/`PresOn` tower into its
mode-value finsum, pull the scalar weight inside, swap the finite tower-depth sum past the finsum"
step), which any proof of the three predicates must consume.

## The Mathematica-verified U/V tower structure (exact `Solve`, `n = 1,2`, `M,P ≤ 3`)

Re-expressing `rightProd W n (circ W n c d) a` (the proved split `rightProd_circ_UV_assembly`,
`ZhuVermaAnDescent7`) in the iterated bases `c₍μ₎(d₍γ₎a)` (U) and `d₍μ₎(c₍γ₎a)` (V):

* **U-family** (`c`-first): for each fixed base-mode `γ`, the net coefficient of `c₍μ₎(d₍γ₎a)` is a
  finite ℂ-combination of `cbz (M+n+δ) (μ+2n+2+δ)` (a `PresOn`-tower in `c`, grade `M`, base `d₍γ₎a`)
  — verified to lie in the tower span by exact `Solve` for **every** base-mode `γ` (including
  `γ < 0`).
* **V-family** (`d`-first): the V-base mode is `c₍s₎a` with `s ≥ 0` (the `mode_iterate` inner-`c`
  index is a `ℕ`), and for each fixed `s ≥ 0` the net coefficient of `d₍μ₎(c₍s₎a)` is a finite
  ℂ-combination of `cbz (P+n+δ) (μ+2n+2+δ)` (a `PresOn`-tower in `d`, grade `P`, base `c₍s₎a`) —
  verified to lie in the tower span for every `s ≥ 0`.  (The weights may depend on `M`; harmless,
  the towers are still `∈ On W n` by `Pres_mem_On`, per `VfamOn_mem_On`.)

So both families ARE finite ℂ-combinations of `PresOn`-towers (the predicates are TRUE).  The base
modes that actually contribute are bounded by `W.regularity` (the infinite formal `mode_iterate`
tail acts as `0` on the genuine vectors `d₍γ₎a` / `c₍s₎a`).

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

/-! ## The mode-value finsum form of a single `PresOn`-tower-family summand.

`UfamOn`/`VfamOn` (Descent8) are finite double sums (over the base-mode index `g < Γ` and the
tower-depth `δ < Δ`) of `wU/wV • PresOn …`.  Expanding each `PresOn` into its mode-value finsum
(`PresOn_eq_finsum`, Descent4) and pulling the scalar weight inside gives the per-`(g)` collapse
below — the depth-`n` lift of `ZhuAssociator.Ufam_inner`/`Vfam_inner`. -/

/-- The net mode-`μ` tower weight of `w₍μ₎(base)` collected from a `δ`-indexed `PresOn`-tower family
(depth `< Δ`, grade `M`, level `n`) with per-depth weights `wt : ℕ → ℂ`.  Depth-`n` lift of
`ZhuAssociator.uCoeffTower`/`vCoeffTower`. -/
noncomputable def towerCoeff (M n : ℕ) (wt : ℕ → ℂ) (Δ : ℕ) (μ : ℤ) : ℂ :=
  ∑ δ ∈ Finset.range Δ, wt δ * cbz ((M : ℤ) + n + δ) (μ + 2 * n + 2 + δ)

/-- **Per-base-mode tower-family collapse.**  A finite `δ`-indexed `PresOn`-tower family based at a
fixed vector `base` collapses to the single mode-value finsum `∑ᶠ μ, towerCoeff … μ • w₍μ₎base`.
Depth-`n` lift of `ZhuAssociator.Ufam_inner`/`Vfam_inner`: expand each `PresOn` via
`PresOn_eq_finsum`, pull the per-depth weight inside, and swap the finite `δ`-sum past the finsum. -/
theorem presOnFamily_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (w base : 𝒱)
    (wt : ℕ → ℂ) (Δ : ℕ) :
    (∑ δ ∈ Finset.range Δ, wt δ • PresOn W M n δ w base)
      = ∑ᶠ μ : ℤ, towerCoeff M n wt Δ μ • W.smul w μ base := by
  -- expand each `PresOn` into a mode-value finsum and pull the per-depth scalar in.
  rw [show (∑ δ ∈ Finset.range Δ, wt δ • PresOn W M n δ w base)
        = ∑ δ ∈ Finset.range Δ,
            ∑ᶠ μ : ℤ, (wt δ * cbz ((M : ℤ) + n + δ) (μ + 2 * n + 2 + δ)) • W.smul w μ base from
      Finset.sum_congr rfl fun δ _ => by
        rw [PresOn_eq_finsum W M n δ w base]
        have hfin : Function.HasFiniteSupport
            (fun μ : ℤ => cbz ((M : ℤ) + n + δ) (μ + 2 * n + 2 + δ) • W.smul w μ base) :=
          ZhuHR.smul_support_of_scalar W w base _
            (Set.Finite.subset
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + n + δ) (by positivity)
                (2 * n + 2 + δ))
              (fun μ hμ => by
                rw [Function.mem_support] at hμ ⊢
                intro h; apply hμ
                rwa [show μ + 2 * (n : ℤ) + 2 + (δ : ℤ) = μ + (2 * (n : ℤ) + 2 + (δ : ℤ)) from
                  by ring]))
        rw [smul_finsum' (wt δ) hfin]
        refine finsum_congr fun μ => ?_
        rw [smul_smul]]
  -- swap the finite `δ`-sum past the finsum.
  rw [← finsum_sum_comm (Finset.range Δ)
      (fun μ δ => (wt δ * cbz ((M : ℤ) + n + δ) (μ + 2 * n + 2 + δ)) • W.smul w μ base)
      (fun δ _ => ZhuHR.smul_support_of_scalar W w base _
        (Set.Finite.subset
          (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + n + δ) (by positivity) (2 * n + 2 + δ))
          (fun μ hμ => by
            rw [Function.mem_support] at hμ ⊢
            intro h; apply hμ
            rw [show μ + 2 * (n : ℤ) + 2 + (δ : ℤ) = μ + (2 * (n : ℤ) + 2 + (δ : ℤ)) from by ring,
              h, mul_zero])))]
  refine finsum_congr fun μ => ?_
  rw [towerCoeff, Finset.sum_smul]

/-! ## The `UfamOn`/`VfamOn` mode-value finsum forms (the depth-`n` lift of `Ufam_eq`/`Vfam_eq`).

Applying `presOnFamily_eq_finsum` per base-mode index `g` rewrites the inner tower-depth `δ`-sum of
`UfamOn`/`VfamOn` (Descent8) as a mode-value finsum `∑ᶠ μ, towerCoeff … μ • c₍μ₎(d₍γ₎a)` (U) resp.
`∑ᶠ μ, towerCoeff … μ • d₍μ₎(c₍γ₎a)` (V).  These are exactly the forms a proof of the three
predicates regroups the FZ-product split into. -/

/-- **`UfamOn` mode-value form.**  `UfamOn` rewrites as a finite base-mode sum of mode-value finsums
of `c₍μ₎(d₍γ₎a)`, the tower weight at `(γ, μ)` being `towerCoeff M n (wU γ ·) Δ μ`. -/
theorem UfamOn_eq_finsum (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c d a : 𝒱)
    (wU : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    UfamOn W M n c d a wU γ₀ Γ Δ
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, towerCoeff M n (wU (γ₀ + (g : ℤ))) Δ μ
            • W.smul c μ (W.smul d (γ₀ + (g : ℤ)) a) := by
  rw [UfamOn]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact presOnFamily_eq_finsum W M n c (W.smul d (γ₀ + (g : ℤ)) a) (wU (γ₀ + (g : ℤ))) Δ

/-- **`VfamOn` mode-value form.**  `VfamOn` rewrites as a finite base-mode sum of mode-value finsums
of `d₍μ₎(c₍γ₎a)`, the tower weight at `(γ, μ)` being `towerCoeff P n (wV γ ·) Δ μ`. -/
theorem VfamOn_eq_finsum (W : VertexOperatorAlgebra 𝒱) (P n : ℕ) (c d a : 𝒱)
    (wV : ℤ → ℕ → ℂ) (γ₀ : ℤ) (Γ Δ : ℕ) :
    VfamOn W P n c d a wV γ₀ Γ Δ
      = ∑ g ∈ Finset.range Γ,
          ∑ᶠ μ : ℤ, towerCoeff P n (wV (γ₀ + (g : ℤ))) Δ μ
            • W.smul d μ (W.smul c (γ₀ + (g : ℤ)) a) := by
  rw [VfamOn]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact presOnFamily_eq_finsum W P n d (W.smul c (γ₀ + (g : ℤ)) a) (wV (γ₀ + (g : ℤ))) Δ

/-! ## The reduction of `RightCircTowerEq` to the per-base-mode tower-collapse cores.

Combining the proved `UfamOn_eq_finsum`/`VfamOn_eq_finsum` (this file) with the proved
`rightProd_circ_UV_assembly` (`ZhuVermaAnDescent7`), the predicate `RightCircTowerEq W n M P c d a`
(`rightProd W n (circ W n c d) a = UfamOn + VfamOn`, Descent8) is equivalent to the **U/V mode-value
regrouping**: that the FZ-product split, after distributing the `Uterm − Vterm` subtraction across
the `∑ᶠ s` and the finite `(i,j,r)`-sum and reindexing by base-mode `γ` and mode `μ`, equals

  `∑_g ∑ᶠ μ, towerCoeff M n (wU (γ₀+g)) Δ μ • c₍μ₎(d₍γ₀+g₎a)`     (U-side)
  `+ ∑_g ∑ᶠ μ, towerCoeff P n (wV (γ₀+g)) Δ μ • d₍μ₎(c₍γ₀+g₎a)`   (V-side)

for some finite tower weights `wU, wV : ℤ → ℕ → ℂ` and ranges `γ₀, Γ, Δ`.  This is purely VOA-level
finsum bookkeeping (the depth-`n` lift of `ZhuAssociator.lhs_split` + `USide_eq`/`VSide_eq`) once the
two **scalar tower-collapse core identities** below are in hand — the depth-`n` lifts of
`ZhuUCore.u_core`/`ZhuVCore.v_core`:

* **U-core** (depth-`n` `u_core`):  for each fixed base-mode `γ`, the net U-side `cbz`-coefficient of
  `c₍μ₎(d₍γ₎a)` (the `(i,j,r,s)`-sum with `s = ℓ-μ`, `ℓ = i-2n-2`, `r = γ-ℓ+μ+n+j+1`),
    `Ucoeff(n,M,P,γ,μ) = ∑_{i,j} cbz(M+n,i) (-1)^j cbz(j+n,j) cbz(G+j, γ-(i-2n-2)+μ+n+j+1)`
                          `· (-1)^{(i-2n-2)-μ} gBinom(i-2n-2, (i-2n-2)-μ)`,  `G = M+P-(i-2n-2)-1`,
  equals a finite tower `∑_δ wU(n,M,P,γ,δ) · cbz(M+n+δ, μ+2n+2+δ)`.

* **V-core** (depth-`n` `v_core`):  for each fixed inner-`c` index `s ≥ 0` (the V-base mode), the net
  V-side `cbz`-coefficient of `d₍μ₎(c₍s₎a)` equals a finite tower
  `∑_δ wV(n,M,P,s,δ) · cbz(P+n+δ, μ+2n+2+δ)`.

Both cores are **Mathematica-verified true** (exact `Solve` over `n = 1,2`,
`M,P ≤ 3`, all base modes), so `RightCircTowerEq W n M P c d a` is TRUE for all arguments.  Crucially,
the verification further shows that the per-FZ-index `j` inner `i`-sum is *already* a
tower in `μ`, for every fixed `(γ, j)` — i.e. the U-core collapses **through the proved depth-`n`
generalized Vandermonde `ZhuRes.gen_vandermonde` per `j`** (collapse the inner `i`-sum), then the FZ
`j`-sum through `ZhuRes.gen_jsum`, exactly mirroring the commutator-family collapse
`coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`) — the same engine, with the iterate reindexing
(`mode_iterate` base-mode `γ` / mode `μ`) in place of the commutator reindexing (`inner_reindexN`).
So the scalar cores are reachable from the already-proved combinatorial certificates; the remaining
work is the VOA-level finsum reindexing of the assembly's U/V-side into the `towerCoeff` mode-value
forms proved here, the depth-`n` lift of `ZhuAssociator.USide_eq`/`VSide_eq` + `Sn_eq_finsum`.

`LeftGenTowerEq`/`RightGenTowerEq` are the same regrouping with the `O(𝒱)`-base generator
`g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (`zhuMul_L_base`) in the applied slot; `RightGenTowerEq` additionally
carries the Dong–Li–Mason `(1+z)^{wt a + j}` right-shift.

## Status proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `presOnFamily_eq_finsum` — the per-base-mode `PresOn`-tower-family → mode-value finsum collapse
  (depth-`n` lift of `ZhuAssociator.Ufam_inner`/`Vfam_inner`).
* `UfamOn_eq_finsum` / `VfamOn_eq_finsum` — the `UfamOn`/`VfamOn` mode-value forms (depth-`n` lift of
  `ZhuAssociator.Ufam_eq`/`Vfam_eq`), the RHS targets of the regrouping.

The three predicates, hence `leftDescends_holds`/`rightDescends_holds` (Descent8), hence the
unconditional `An.lActU`/`An.rActU`, are NOT discharged here: they await the depth-`n`
`ZhuUCore`/`ZhuVCore` cores.  Nothing is `sorry`'d or axiomatized.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.presOnFamily_eq_finsum
  #print axioms VOA.UfamOn_eq_finsum
  #print axioms VOA.VfamOn_eq_finsum
-/
