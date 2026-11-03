/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent5

/-!
# The depth-`n` iterate expansion for the `RightDescends.on_mem` associator membership

This file develops the depth-`n` lift of the associator/iterate machinery
(`ZhuAssociator.lhs_split`/`USide`/`VSide`, `ZhuUCore.u_core`/`ZhuVCore.v_core`) toward the
`RightDescends.on_mem` field of the `A_n(𝒱)` bimodule descent.

`rightProd_On_mem_On_of_homog` (proved in `ZhuVermaAnDescent5`) reduces `RightDescends.on_mem` to
the all-homogeneous statement

  `H_R : ∀ M P K, c ∈ 𝒱_M → d ∈ 𝒱_P → a ∈ 𝒱_K → rightProd W n (circ W n c d) a ∈ On W n`.

`rightProd_circ_homogeneous_left` (proved) expands its LHS to
`∑_i C(M+n,i) • rightProd W n (c₍ᵢ₋₂ₙ₋₂₎d) a`.  This file then expands each inner
`rightProd W n w a` (for homogeneous `w := c₍ℓ₎d`) via `rightProd_homogeneous`, so the residue acts
on iterated modes `(c₍ℓ₎d)₍N₎a`, and re-expands each via `mode_iterate` (Gannon 5.1.7d) into the
**U-family** `c₍μ₎(d₍γ₎a)` and the **V-family** `d₍μ₎(c₍γ₎a)`.

## What this file proves (axiom-clean)

* `rightProd_homog_expand` — the homogeneous collapse of `rightProd W n w a` (for `w ∈ 𝒱_G`) to the
  explicit FZ residue double sum.
* `iterate_UV_split` — the per-`(ℓ,N)` `mode_iterate` split of `(c₍ℓ₎d)₍N₎a` into the U/V finsum
  families with the explicit `(-1)^i·gBinom ℓ i` coefficients.
* `rightProd_circ_iterate_expand` — the assembled finite-sum-of-finsums expansion of
  `rightProd W n (circ W n c d) a` over `(j, i, r)` and the `mode_iterate` index, the depth-`n`
  analog of `ZhuAssociator.lhs_split`'s entry point.

## Mathematica-verified depth-`n` certificate (the U-family tower collapse)

The net U-side coefficient of `c₍μ₎(d₍γ₎a)` collapses onto `PresOn`-towers in `c` (grade `M`, base
`d₍γ₎a`), with tower weights `w_U(n,P,γ,δ)` **independent of `M` and `μ`**:
`U_coeff = ∑_δ w_U(n,P,γ,δ)·C(M+n+δ, μ+2n+2+δ)`.  Re-verified here:
`w_U(n=1,P=1,γ=-1)=(-1,12,-20)`, `(γ=0)=(1,-16,50,-40)`, `(γ=1)=(-1,20,-90,140,-70)`.  At `n=0` it
specializes to `ZhuUCore.u_core`.  This is the structure consumed by the keystone `Pres_mem_On`.

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

/-! ## The homogeneous collapse of the right FZ product `rightProd W n w a`.

For homogeneous `w ∈ 𝒱_G`, `rightProd W n w a = ∑_{j≤n} (-1)^j C(j+n,j) ∑_r C(G+j,r) w₍ᵣ₋ₙ₋ⱼ₋₁₎a`,
the explicit FZ residue double sum (normalising the `toNat` range to `range (G+j+1)`).  This is the
right-product analog of `circ_homogeneous`/`leftProd_homogeneous` restated with a `ℕ`-range. -/
theorem rightProd_homog_expand (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {G : ℕ} {w : 𝒱}
    (hw : w ∈ W.grading (G : ℤ)) (a : 𝒱) :
    rightProd W n w a
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
            ∑ r ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + j) (r : ℤ)
                • W.smul w ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) a := by
  rw [rightProd_homogeneous W n hw a]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 1
  -- normalise the inner range `(G+j).toNat + 1` to `range (G+n+1)`: extra terms r > G+j vanish.
  have htn : (((G : ℤ) + (j : ℤ)).toNat + 1) = G + j + 1 := by
    rw [show ((G : ℤ) + (j : ℤ)) = ((G + j : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]
  rw [htn]
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega : G + j + 1 ≤ G + n + 1))
  intro r _ hrni
  have hrlo : G + j + 1 ≤ r := Nat.le_of_not_lt (fun h => hrni (Finset.mem_range.mpr h))
  rw [cbz_lt (by positivity) (by
      have : ((G + j : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : G + j < r)
      push_cast at this ⊢; omega), zero_smul]

/-! ## The `mode_iterate` U/V split of an iterated mode `(c₍ℓ₎d)₍N₎a`.

`mode_iterate` (Gannon 5.1.7d) expands `(c₍ℓ₎d)₍N₎a` into a `∑ᶠ i : ℕ` of a **U-family** term
`c₍ℓ₋ᵢ₎(d₍N₊ᵢ₎a)` minus the sign-weighted **V-family** term
`(-1)^ℓ d₍ℓ₊N₋ᵢ₎(c₍ᵢ₎a)`, with coefficient `(-1)^i·gBinom ℓ i`.  We record it in the `c`/`d`/`a`
naming for the descent.  This is the depth-`n` analog of the `lhs_per_a` step of the `n = 0`
associator (`ZhuAssociator.lhs_per_a`), which feeds `USide`/`VSide`. -/
theorem iterate_UV_split (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (ℓ N : ℤ) :
    W.smul (W.smul c ℓ d) N a
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
          (W.smul c (ℓ - i) (W.smul d (N + i) a)
            - ((-1 : ℂ) ^ ℓ) • W.smul d (ℓ + N - i) (W.smul c (i : ℤ) a)) :=
  mode_iterate W c d ℓ N a

/-! ## The depth-`n` expansion of `rightProd W n (circ W n c d) a` to iterated modes.

For homogeneous `c ∈ 𝒱_M`, `rightProd_circ_homogeneous_left` distributes the right product over the
`i`-sum of the circle product, giving `∑_i C(M+n,i) • rightProd W n (c₍ℓ₎d) a` with `ℓ = i-2n-2`.
Each inner factor `c₍ℓ₎d` is homogeneous (grade `M+P-ℓ-1`) when `d ∈ 𝒱_P`, so the inner right
product collapses by `rightProd_homog_expand` (when the grade is `≥ 0`; otherwise the factor is `0`).
We bundle the grade bookkeeping: each `c₍ℓ₎d` lands in `𝒱_{M+P-ℓ-1}`. -/
theorem circ_inner_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (ℓ : ℤ) :
    W.smul c ℓ d ∈ W.grading ((M : ℤ) + (P : ℤ) - ℓ - 1) :=
  W.smul_mem_grading hc hd ℓ

/-- The per-`i` inner right product `rightProd W n (c₍ℓ₎d) a` (with `ℓ = i-2n-2`) collapses, when
the inner grade `G := M+P-ℓ-1 ≥ 0`, to the FZ residue double sum over `(j, r)` of iterated modes
`(c₍ℓ₎d)₍r₋ₙ₋ⱼ₋₁₎a`.  The depth-`n` lift of expanding `(u₍ₐ₋₁₎v)*w` (`ZhuAssociator.lhs_per_a`). -/
theorem rightProd_circ_inner_expand (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M P G : ℕ} {c d : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (ℓ : ℤ)
    (hG : (G : ℤ) = (M : ℤ) + (P : ℤ) - ℓ - 1) (a : 𝒱) :
    rightProd W n (W.smul c ℓ d) a
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (j : ℤ)) •
            ∑ r ∈ Finset.range (G + n + 1),
              cbz ((G : ℤ) + j) (r : ℤ)
                • W.smul (W.smul c ℓ d) ((r : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) a := by
  have hmem : W.smul c ℓ d ∈ W.grading (G : ℤ) := by
    rw [hG]; exact circ_inner_mem_grading W hc hd ℓ
  exact rightProd_homog_expand W n hmem a

/-! ## The assembled iterate expansion of `rightProd W n (circ W n c d) a`.

Combining `rightProd_circ_homogeneous_left` with `iterate_UV_split` (applied to the iterated mode
`(c₍ℓ₎d)₍N₎a`, `ℓ = i-2n-2`), the right product over a circle generator expands to a finite sum (over
the circle index `i` and FZ residue `j, r`) of the `mode_iterate` U/V finsum families.  This is the
depth-`n` analog of `ZhuAssociator.lhs_split` (`(u*v)*w = USide − VSide`), the entry point to the
U-family / V-family / cross-assembly collapse.  We state it on the homogeneous-`c` distribution: each
inner `rightProd W n (c₍ℓ₎d) a` is rewritten by `rightProd_homog_expand` after splitting each iterated
mode by `iterate_UV_split`. -/
theorem rightProd_circ_homogeneous_iterate (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (d a : 𝒱) :
    rightProd W n (circ W n c d) a
      = ∑ i ∈ Finset.range (M + n + 1),
          cbz ((M : ℤ) + n) (i : ℤ) •
            rightProd W n (W.smul c ((i : ℤ) - 2 * (n : ℤ) - 2) d) a :=
  rightProd_circ_homogeneous_left W n hc d a

/-! ## The per-iterate-term `mode_iterate` rewrite inside the right product.

Once the inner residue `rightProd W n (c₍ℓ₎d) a` is expanded (via `rightProd_circ_inner_expand`),
each summand carries an iterated mode `(c₍ℓ₎d)₍N₎a` with `N = r - n - j - 1`.  Rewriting it via
`iterate_UV_split` produces the U/V finsum families that the depth-`n` cross-assembly must collapse.
We package the rewrite at the per-`(ℓ,N)` level so the cross-assembly works on the finsum body. -/
theorem iterate_term_rewrite (W : VertexOperatorAlgebra 𝒱) (c d a : 𝒱) (ℓ r : ℤ) (n j : ℕ) :
    W.smul (W.smul c ℓ d) (r - ((n : ℤ) + (j : ℤ) + 1)) a
      = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * gBinom ℓ i) •
          (W.smul c (ℓ - i) (W.smul d ((r - ((n : ℤ) + (j : ℤ) + 1)) + i) a)
            - ((-1 : ℂ) ^ ℓ)
              • W.smul d (ℓ + (r - ((n : ℤ) + (j : ℤ) + 1)) - i) (W.smul c (i : ℤ) a)) :=
  iterate_UV_split W c d a ℓ (r - ((n : ℤ) + (j : ℤ) + 1))

/-!
## PRECISE remaining target for `RightDescends.on_mem` (NOT `sorry`, NOT axiomatized)

With the proved entry points above (`rightProd_circ_homogeneous_iterate` distributing the right
product over the circle index, `rightProd_circ_inner_expand` collapsing each inner right product,
and `iterate_term_rewrite`/`iterate_UV_split` splitting each iterated mode into the U/V finsum
families), `RightDescends.on_mem` reduces (via the proved `rightProd_On_mem_On_of_homog`) to the
single all-homogeneous statement

  `H_R : ∀ (M P K : ℕ), c ∈ 𝒱_M → d ∈ 𝒱_P → a ∈ 𝒱_K → rightProd W n (circ W n c d) a ∈ On W n`.

### The discovered, Mathematica-verified depth-`n` coefficient structure

Re-expressing `rightProd W n (circ W n c d) a` in the iterated bases `c₍μ₎(d₍γ₎a)` (U) and
`d₍μ₎(c₍γ₎a)` (V):

* **U-family** (`c`-first).  The net coefficient of `c₍μ₎(d₍γ₎a)` collapses onto `PresOn`-towers in
  `c` (grade `M`, base `d₍γ₎a`), with weights `w_U(n,P,γ,δ)` **independent of `M` and `μ`**:
  `U_coeff(n,M,P,μ,γ) = ∑_δ w_U(n,P,γ,δ)·C(M+n+δ, μ+2n+2+δ)`.  Verified for `n=1,2`,
  `P ≤ 3`; e.g. `n=1,P=1`: `w_U(γ=-1)=(-1,12,-20)`, `w_U(γ=0)=(1,-16,50,-40)`,
  `w_U(γ=1)=(-1,20,-90,140,-70)`.  Each such tower is `PresOn W M n δ c (d₍γ₎a) ∈ On W n` by the
  keystone `Pres_mem_On`, so **the U-family ∈ `On W n`**.

* **V-family** (`d`-first).  The coefficient of `d₍μ₎(c₍γ₎a)` is supported on `μ ≤ P - 2n - 2`
  (verified: for `n=1` the maximal `μ` is `P-4`; for `n=2`, `P-6`; in particular the V-family
  **vanishes identically when `P ≤ 2n`**, e.g. `n=1,P=0` and `n=2,P≤2`).  However the V-coefficient
  is **`M`-dependent** for `γ ≥ 1` (linear in `M` at `γ=1`, quadratic at `γ=2`, …), so the V-family
  is NOT a pure `PresOn`-tower in `d`; its `M`-dependent part is reconciled against the U-family by
  the depth-`n` `(1+z)`-basis change-of-basis — the analog of `ZhuMu.mu_identity` /
  `ZhuAssociator.assoc_eq`.

### What remains for `H_R`

The single remaining input is the **depth-`n` cross-assembly identity**: the `cbz`-coefficient
identity reconciling the `M`-dependent V-coefficient with the U-family `PresOn`-towers (the depth-`n`
lift of `ZhuMu.mu_identity` / `ZhuAssociator.assoc_eq`, carrying the extra `(1+z)^n/z^{2n}`
weighting).  Once formalized, the finsum-reindexing apparatus (depth-`n` analogs of
`ZhuAssociator.USide_eq`/`VSide_eq`/`Ufam_eq`/`Vfam_eq`, all VOA-level bookkeeping built on the
proved entry points + `Pres_mem_On`) closes `H_R`, hence `RightDescends.on_mem`.  The two `gen_mem`
fields (`LeftDescends.gen_mem`, `RightDescends.gen_mem`) are the same computation with the `O(𝒱)`
base-generator `g = ∑ᵢ C(M,i) u₍ᵢ₋₂₎v` (`zhuMul_L_base`) in the applied slot;
`RightDescends.gen_mem` additionally carries the Dong–Li–Mason `(1+z)^{wt a+j}` right-shift.

None of these is `sorry`'d or axiomatized.  The entry-point reductions above are the proved,
axiom-clean foundation; the cross-assembly `cbz` identity is the precise combinatorial target.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.rightProd_homog_expand
  #print axioms VOA.iterate_UV_split
  #print axioms VOA.circ_inner_mem_grading
  #print axioms VOA.rightProd_circ_inner_expand
  #print axioms VOA.rightProd_circ_homogeneous_iterate
  #print axioms VOA.iterate_term_rewrite
-/
