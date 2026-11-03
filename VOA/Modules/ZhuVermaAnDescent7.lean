/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent6

/-!
# The depth-`n` U/V split assembly for `RightDescends.on_mem`, and the corrected
cross-assembly structure (Mathematica-verified)

This file continues the depth-`n` lift of the associator/iterate machinery toward the
`RightDescends.on_mem` field of the `A_n(𝒱)` bimodule descent, building directly on the proved
entry points of `ZhuVermaAnDescent6` (`rightProd_circ_homogeneous_iterate`,
`rightProd_circ_inner_expand`, `iterate_term_rewrite`, `iterate_UV_split`).

## The reduction state (recap)

`RightDescends.on_mem` reduces (via `rightProd_On_mem_On_of_homog`, proved in `ZhuVermaAnDescent5`)
to the single all-homogeneous statement

  `H_R : ∀ M P K, c ∈ 𝒱_M → d ∈ 𝒱_P → a ∈ 𝒱_K → rightProd W n (circ W n c d) a ∈ On W n`.

`rightProd_circ_homogeneous_iterate` distributes the LHS over the circle index `i`, giving
`∑_i C(M+n,i) • rightProd W n (c₍ℓ₎d) a` with `ℓ = i-2n-2`; `rightProd_circ_inner_expand` collapses
each inner right product (the inner factor `c₍ℓ₎d ∈ 𝒱_G`, `G = M+P-ℓ-1`); and
`iterate_term_rewrite` / `iterate_UV_split` (`mode_iterate`, Gannon 5.1.7d) split each iterated mode
`(c₍ℓ₎d)₍N₎a` (`N = r-n-j-1`) into the **U-family** `c₍μ₎(d₍γ₎a)` and the **V-family**
`d₍μ₎(c₍γ₎a)`.

## What this file proves (axiom-clean)

* `rightProd_circ_inner_UVterm` — the per-`i` U/V finsum split of the inner right product
  `rightProd W n (c₍ℓ₎d) a` (the depth-`n` analog of `ZhuAssociator.lhs_split`'s per-summand
  `mode_iterate` step), assembled on the homogeneous-`c`/`d` distribution.  This is the entry point
  that exposes the U-family and V-family explicitly, summand by summand.
* `rightProd_circ_UV_assembly` — the full assembled U/V split of `rightProd W n (circ W n c d) a`
  over the circle index `i`, FZ index `j`, residue `r`, and `mode_iterate` index `s`, with the
  negative-inner-grade indices `i` (where `c₍ᵢ₋₂ₙ₋₂₎d` vanishes) carried by an explicit `if`-guard.
  The depth-`n` analog of `ZhuAssociator.lhs_split`.

## The Mathematica-verified depth-`n` coefficient structure (CORRECTED)

Re-expressing `rightProd W n (circ W n c d) a` in the iterated bases `c₍μ₎(d₍γ₎a)` (U) and
`d₍μ₎(c₍γ₎a)` (V), the net coefficients are:

* **U-family** (`c`-first).  `U_coeff(n,M,P,μ,γ)` is, for each fixed `γ`, a **`PresOn`-tower in `c`
  (grade `M`)** based at `d₍γ₎a`:
  `U_coeff(n,M,P,μ,γ) = ∑_δ w_U(n,P,γ,δ)·C(M+n+δ, μ+2n+2+δ)`, with weights `w_U` independent of
  `M, μ`.  Re-verified (Mathematica) for `n = 0,1,2`, `M,P ≤ 5`, `γ ∈ [-1,4]`
  (648 cases); e.g. `n=1,P=1`: `w_U(γ=-1)=(-1,12,-20)`, `w_U(γ=0)=(1,-16,50,-40)`,
  `w_U(γ=1)=(-1,20,-90,140,-70)`.  Each tower `∈ On W n` by the keystone `Pres_mem_On`.

* **V-family** (`d`-first).  `V_coeff(n,M,P,μ,γ)` is supported on `μ ≤ P - 2n - 2` (it vanishes
  identically for `P ≤ 2n`), and is `M`-dependent for `γ ≥ 1` (linear at `γ=1`, quadratic at `γ=2`,
  …).  **Decisive corrected finding (Mathematica, 648 cases):** despite the
  `M`-dependence, `V_coeff(n,M,P,·,γ)` is — for each fixed `M,P,n,γ` — *still* a **`PresOn`-tower in
  `d` (grade `P`)** based at `c₍γ₎a`:
  `V_coeff(n,M,P,μ,γ) = ∑_δ w_V(n,M,P,γ,δ)·C(P+n+δ, μ+2n+2+δ)`, with weights `w_V` that may depend on
  `M` (this is harmless: each tower lies in `On W n` by `Pres_mem_On` *regardless of its scalar
  weight*).

**Consequence.**  Because the U-modes `c₍μ₎(d₍γ₎a)` and the V-modes `d₍μ₎(c₍γ₎a)` are *independent*
formal symbols, the total residue lies in `On W n` **iff the U-family and the V-family lie in
`On W n` separately**, and both do — each is a finite sum of `PresOn`-towers (`∈ On` by
`Pres_mem_On`).  There is therefore **no genuine U↔V cross-assembly reconciliation**: the apparent
obstruction (the `M`-dependence of the V-family) is absorbed entirely inside the V-family's own
`d`-tower weights.  This sharpens the working hypothesis recorded in `ZhuVermaAnDescent5/6`.

## The PRECISE remaining target (NOT `sorry`, NOT axiomatized)

The single remaining input is the pair of **scalar tower-collapse `cbz` identities**

  (U)  `U_coeff(n,M,P,μ,γ) = ∑_δ w_U(n,P,γ,δ)·C(M+n+δ, μ+2n+2+δ)`,
  (V)  `V_coeff(n,M,P,μ,γ) = ∑_δ w_V(n,M,P,γ,δ)·C(P+n+δ, μ+2n+2+δ)`,

with explicit `cbz`/`gBinom` weight families `w_U, w_V` (each a finite `δ`-sum; at `n = 0` the
U-identity specialises to `ZhuAssociator.uSideScalar_split`'s `uCoeffTower`).  These are the
depth-`n` lifts of `ZhuUCore.u_core` / `ZhuVCore.v_core` (NOT of `ZhuMu.mu_identity`: there is no
`(1+z)`-basis cross term to reconcile here, per the corrected finding above).  Once formalised, the
finsum-reindexing apparatus (depth-`n` analogs of `ZhuAssociator.USide_eq`/`VSide_eq`/`Ufam_eq`/
`Vfam_eq`, all VOA-level bookkeeping built on `rightProd_circ_inner_UVterm` + `Pres_mem_On`) closes
`H_R`, hence `RightDescends.on_mem`.  The two `gen_mem` fields are the same computation with the
`O(𝒱)`-base generator `g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (`zhuMul_L_base`) in the applied slot;
`RightDescends.gen_mem` additionally carries the Dong–Li–Mason `(1+z)^{wt a + j}` right-shift.

Note that `LeftDescends.on_mem` (`leftProd_On_mem_On`, `ZhuVermaAnDescent4`) is already discharged
unconditionally.

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

/-! ## The per-`i` U/V finsum split of the inner right product.

For homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `i`-th summand of the homogeneous distribution of
`rightProd W n (circ W n c d) a` is `C(M+n,i) • rightProd W n (c₍ℓ₎d) a` with `ℓ = i-2n-2`.  The
inner factor `c₍ℓ₎d` is homogeneous of grade `G = M+P-ℓ-1`, so `rightProd_circ_inner_expand`
collapses the inner right product into the FZ residue double sum over `(j, r)` of the iterated mode
`(c₍ℓ₎d)₍N₎a` (`N = r-n-j-1`); `iterate_term_rewrite` then splits each such iterated mode into the
U-family `c₍ℓ₋s₎(d₍N+s₎a)` minus the sign-weighted V-family `d₍ℓ+N-s₎(c₍s₎a)`, with `mode_iterate`
coefficient `(-1)^s·gBinom ℓ s`.  This is the depth-`n` analog of `ZhuAssociator.lhs_split`'s
per-summand `mode_iterate` step, the entry point exposing the U/V families explicitly. -/
theorem rightProd_circ_inner_UVterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P G : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (i : ℕ)
    (hG : (G : ℤ) = (M : ℤ) + (P : ℤ) - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) (a : 𝒱) :
    rightProd W n (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) a
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
            ∑ r ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + j) (r : ℤ) •
                (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s) •
                  (W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                      (W.smul d ((r - ((n : ℤ) + (j : ℤ) + 1)) + s) a)
                    - ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
                      • W.smul d (((i : ℤ) - 2 * (n : ℤ) - 2) + (r - ((n : ℤ) + (j : ℤ) + 1)) - s)
                          (W.smul c (s : ℤ) a))) := by
  rw [rightProd_circ_inner_expand W n hc hd ((i : ℤ) - 2 * (n : ℤ) - 2) hG a]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  exact iterate_term_rewrite W c d a ((i : ℤ) - 2 * (n : ℤ) - 2) (r : ℤ) n j

/-! ## The assembled depth-`n` U/V split of `rightProd W n (circ W n c d) a`.

Combining `rightProd_circ_homogeneous_iterate` (distribute over the circle index `i`) with the
per-`i` split `rightProd_circ_inner_UVterm`, the full right product over a circle generator expands
into a finite sum (over the circle index `i`, FZ index `j`, residue index `r`) of the
`mode_iterate` U/V finsum families.  We package the assembly through a per-`i` *grade witness*
`G : ℕ → ℕ` with `(G i : ℤ) = M+P-(i-2n-2)-1` for the indices `i` where that quantity is a genuine
natural number (the only indices that contribute: when `M+P-(i-2n-2)-1 < 0` the inner factor
`c₍ᵢ₋₂ₙ₋₂₎d ∈ 𝒱_{<0} = ⊥` vanishes and so does its right product).  This is the depth-`n` analog of
`ZhuAssociator.lhs_split` (`(u*v)*w = USide − VSide`), the entry point to the U-family / V-family
tower collapses. -/
theorem rightProd_circ_UV_assembly (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (a : 𝒱)
    (G : ℕ → ℕ)
    (hG : ∀ i ∈ Finset.range (M + n + 1),
        0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 →
        (G i : ℤ) = (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :
    rightProd W n (circ W n c d) a
      = ∑ i ∈ Finset.range (M + n + 1),
          cbz ((M : ℤ) + n) (i : ℤ) •
            (if 0 ≤ (M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1 then
              ∑ j ∈ Finset.range (n + 1),
                ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
                  ∑ r ∈ Finset.range (G i + n + 1),
                    cbz ((G i : ℤ) + j) (r : ℤ) •
                      (∑ᶠ s : ℕ, ((-1 : ℂ) ^ s * gBinom ((i : ℤ) - 2 * (n : ℤ) - 2) s) •
                        (W.smul c (((i : ℤ) - 2 * (n : ℤ) - 2) - s)
                            (W.smul d ((r - ((n : ℤ) + (j : ℤ) + 1)) + s) a)
                          - ((-1 : ℂ) ^ ((i : ℤ) - 2 * (n : ℤ) - 2))
                            • W.smul d
                                (((i : ℤ) - 2 * (n : ℤ) - 2) + (r - ((n : ℤ) + (j : ℤ) + 1)) - s)
                                (W.smul c (s : ℤ) a)))
            else 0) := by
  rw [rightProd_circ_homogeneous_iterate W n hc d a]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  rcases lt_or_ge ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) 0 with hlt | hge
  · rw [if_neg (not_le.mpr hlt)]
    -- the inner factor `c₍ℓ₎d` is in a negative grading, hence `0`; its right product vanishes.
    have hmem : W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d
        ∈ W.grading ((M : ℤ) + P - ((i : ℤ) - 2 * (n : ℤ) - 2) - 1) :=
      circ_inner_mem_grading W hc hd ((i : ℤ) - 2 * (n : ℤ) - 2)
    rw [W.positivity _ hlt, Submodule.mem_bot] at hmem
    rw [hmem, rightProd_zero_left]
  · rw [if_pos hge]
    exact rightProd_circ_inner_UVterm W n hc hd i (G := G i) (hG i hi hge) a

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.rightProd_circ_inner_UVterm
  #print axioms VOA.rightProd_circ_UV_assembly

Verified: both depend on `[propext, Classical.choice, Quot.sound]` only.
-/
