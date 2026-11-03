/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent11

/-!
# The homogeneity-aware per-iterate reduction of `LeftGenTowerEq_holds` /
`RightGenTowerEq_holds`.

This file continues `Modules.ZhuVermaAnDescent11` (the `O(𝒱)`-generator entry points
`leftGenProd_homogeneous_expand`/`rightGenProd_homogeneous_expand`, the closure lemmas
`LeftGenTowerEq_smul_left`/`RightGenTowerEq_smul_right` + `LeftGenTowerEq_sum`/`RightGenTowerEq_sum`,
and the per-iterate reduction criteria `LeftGenTowerEq_of_iterate`/`RightGenTowerEq_of_iterate`).

## The homogeneity of the acting iterate

Descent11 reduced each `gen_mem` predicate to the per-iterate tower decomposition
`LeftGenTowerEq W n (u₍ᵢ₋₂₎v) b` (resp. `RightGenTowerEq W n x (u₍ᵢ₋₂₎v)`), `i < M+1`.  The acting
iterate `u₍ᵢ₋₂₎v` is, by **VA1** (`smul_mem_grading`, Gannon Def. 5.1.3(a)), *homogeneous* whenever
`u ∈ 𝒱_M`, `v ∈ 𝒱_P`:

  `u₍ᵢ₋₂₎v ∈ 𝒱_{M+P-(i-2)-1}`     (`iterate_mem_grading`).

So the genuine remaining content of each `gen_mem` predicate is the **per-iterate tower decomposition
for a HOMOGENEOUS acting vector** — exactly the same shape as the circle-case target
`RightCircTowerEq_holds` (`ZhuVermaAnDescent10`), whose acting vector is the homogeneous circle
product.  This file packages that observation as the precise homogeneous-iterate hypotheses
`LeftGenTowerEq_holds_of_homogIterate`/`RightGenTowerEq_holds_of_homogIterate`, routing the full
`∀-args` predicates through them with no `sorry` and no axiom.

The grade slice `W.grading : ℤ → Submodule ℂ 𝒱` is `ℤ`-indexed, so the homogeneous-iterate hypothesis
is stated over an arbitrary INTEGER grade `K : ℤ` (`iterateGrade M P i` is naturally an integer that
can be negative when `i ≥ M+P+2`); this keeps the routing free of `ℕ`-casting side conditions.

## The DLM `(1+z)^{wt a + j}` right-shift (`RightGenTowerEq` side)

`RightGenTowerEq W n x g` carries the iterate in the *base* slot; the homogeneity of the iterate is
identical (`iterate_mem_grading`), and the `rightProd`-side Dong–Li–Mason `(1+z)^{wt a+j}` right-shift
(the `s = j` binomial shift of `rightProd`, vs the `s = n` shift of `leftProd`) is already baked into
the per-iterate hypothesis `RightGenTowerEq W n x (u₍ᵢ₋₂₎v)` via the definition of `rightProd`.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.1/2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The homogeneous grade of the acting iterate `u₍ᵢ₋₂₎v`.

By **VA1** (`smul_mem_grading`), the iterate `u₍ᵢ₋₂₎v` of homogeneous `u ∈ 𝒱_M`, `v ∈ 𝒱_P` lies in
the grade `M+P-(i-2)-1` slice.  This is the depth-`n`/generator analog of the fact that the circle
product `circ W n c d` of homogeneous `c, d` is homogeneous of grade `M+P-2n-2`. -/

/-- The integer grade of the iterate `u₍ᵢ₋₂₎v` for `u ∈ 𝒱_M`, `v ∈ 𝒱_P`, mode `(i:ℤ)-2`:
`M+P-(i-2)-1`. -/
def iterateGrade (M P : ℕ) (i : ℕ) : ℤ := (M : ℤ) + (P : ℤ) - ((i : ℤ) - 2) - 1

/-- **The acting iterate is homogeneous** (VA1, `smul_mem_grading`): for `u ∈ 𝒱_M`, `v ∈ 𝒱_P`,
`u₍ᵢ₋₂₎v ∈ 𝒱_{iterateGrade M P i}`.  The grade is `M+P-(i-2)-1`. -/
theorem iterate_mem_grading (W : VertexOperatorAlgebra 𝒱) {M P : ℕ} {u v : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (i : ℕ) :
    W.smul u ((i : ℤ) - 2) v ∈ W.grading (iterateGrade M P i) := by
  have := W.smul_mem_grading hu hv ((i : ℤ) - 2)
  rwa [iterateGrade]

/-! ## The homogeneous-iterate per-iterate hypotheses and the routing to `_holds`.

`LeftGenTowerEq_of_iterate`/`RightGenTowerEq_of_iterate` (`ZhuVermaAnDescent11`) reduce the `gen_mem`
predicates to the per-iterate towers `∀ i < M+1, LeftGenTowerEq W n (u₍ᵢ₋₂₎v) b` (resp.
`RightGenTowerEq`).  Combining with `iterate_mem_grading`, the precise remaining content of each
predicate is the **homogeneous-iterate tower decomposition**: a `PresOn`-tower decomposition of
`leftProd W n w b` (resp. `rightProd W n x w`) for a HOMOGENEOUS acting vector `w ∈ 𝒱_K`, `K : ℤ`.
Feeding either hypothesis into `LeftGenTowerEq_of_iterate`/`RightGenTowerEq_of_iterate` yields the
`∀-args` `_holds`. -/

/-- **`LeftGenTowerEq_holds` from the homogeneous-iterate per-iterate cores.**  If, for every
homogeneous acting vector `w ∈ 𝒱_K` (`K : ℤ`) and base `b`, `leftProd W n w b` admits a `PresOn`-tower
decomposition (`LeftGenTowerEq W n w b`), then the full `O(𝒱)`-generator predicate holds for every
`u v b`: `LeftGenTowerEq W n ((L₋₁u+L₀u)*v) b`.  Routes the homogeneous-iterate hypothesis through
`iterate_mem_grading` + `LeftGenTowerEq_of_iterate` (`ZhuVermaAnDescent11`).

This is the precise remaining `LeftGenTowerEq_holds` content: a tower decomposition of `leftProd` of a
HOMOGENEOUS acting vector, the exact analog of the circle-case `RightCircTowerEq_holds`
(`ZhuVermaAnDescent10`). -/
theorem LeftGenTowerEq_holds_of_homogIterate (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hhom : ∀ (K : ℤ) {w : 𝒱}, w ∈ W.grading K → ∀ b : 𝒱, LeftGenTowerEq W n w b)
    {M P : ℕ} {u v : 𝒱} (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (b : 𝒱) :
    LeftGenTowerEq W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b :=
  LeftGenTowerEq_of_iterate W n hu v b
    (fun i _ => Hhom (iterateGrade M P i) (iterate_mem_grading W hu hv i) b)

/-- **`RightGenTowerEq_holds` from the homogeneous-iterate per-iterate cores.**  The base-slot mirror
of `LeftGenTowerEq_holds_of_homogIterate`: if, for every homogeneous base vector `w ∈ 𝒱_K` (`K : ℤ`)
and acting `x`, `rightProd W n x w` admits a `PresOn`-tower decomposition (`RightGenTowerEq W n x w`),
then the full `O(𝒱)`-generator predicate holds for every `x u v`:
`RightGenTowerEq W n x ((L₋₁u+L₀u)*v)`.  Routes through `iterate_mem_grading` +
`RightGenTowerEq_of_iterate` (`ZhuVermaAnDescent11`).

This is the precise remaining `RightGenTowerEq_holds` content (with the Dong–Li–Mason
`(1+z)^{wt a+j}` right-shift baked into `rightProd`): a tower decomposition of `rightProd` of a vector
acting on a HOMOGENEOUS base. -/
theorem RightGenTowerEq_holds_of_homogIterate (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hhom : ∀ (K : ℤ) {w : 𝒱}, w ∈ W.grading K → ∀ x : 𝒱, RightGenTowerEq W n x w)
    {M P : ℕ} {u v : 𝒱} (hu : u ∈ W.grading (M : ℤ)) (hv : v ∈ W.grading (P : ℤ)) (x : 𝒱) :
    RightGenTowerEq W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) :=
  RightGenTowerEq_of_iterate W n hu v x
    (fun i _ => Hhom (iterateGrade M P i) (iterate_mem_grading W hu hv i) x)

/-!
## The PRECISE remaining target (NOT `sorry`, NOT axiomatized)

The two `O(𝒱)`-generator predicates `LeftGenTowerEq_holds`/`RightGenTowerEq_holds` are reduced — by
the proved, axiom-clean `LeftGenTowerEq_holds_of_homogIterate`/`RightGenTowerEq_holds_of_homogIterate`
(this file), on top of the Descent11 per-iterate criteria and `iterate_mem_grading` (this file) — to a
SINGLE homogeneous-acting-vector tower decomposition, identical in shape to the circle-case
`RightCircTowerEq_holds` (`ZhuVermaAnDescent10`):

  (L-hom)  `∀ K : ℤ, ∀ w ∈ 𝒱_K, ∀ b, LeftGenTowerEq W n w b`,
  (R-hom)  `∀ K : ℤ, ∀ w ∈ 𝒱_K, ∀ x, RightGenTowerEq W n x w`.

`(L-hom)`/`(R-hom)` are the genuine depth-`n` **iterate cores** (NOT axioms): for a homogeneous acting
`w ∈ 𝒱_K`, `leftProd W n w b` (resp. `rightProd W n x w`) expands by `leftProd_homogeneous`
(resp. `rightProd_homogeneous`) into the explicit FZ double sum
`∑_{j} (-1)^j C(j+n,n) ∑ᵢ C(K+n,i) w₍ᵢ₋ₙ₋ⱼ₋₁₎b`, and the net per-base-mode `cbz`-coefficient of each
`w₍μ₎b` collapses (via `ZhuRes.gen_vandermonde` per FZ index `j`, then `ZhuRes.gen_jsum`) onto a
`PresOn`-tower — exactly mirroring `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`) and the
`RightCircTowerEq` U/V cores (`UgammaModeColl = towerCoeff`, `VgammaModeColl = towerCoeff`,
`ZhuVermaAnDescent10`).  They are the depth-`n` lift of the ~470-line
`coeffSn_eq_coeffPn` + `Sn_eq_finsum` + `PresOnCombo_eq_finsum` chain.  Left here as precise stated
targets, NOT `sorry`'d and NOT axiomatized; faking them would violate the no-holes hard rules.

Once `(L-hom)`/`(R-hom)` are supplied, `LeftGenTowerEq_holds_of_homogIterate`/
`RightGenTowerEq_holds_of_homogIterate` (this file) give `LeftGenTowerEq_holds`/`RightGenTowerEq_holds`,
which — together with `RightCircTowerEq_holds` (the circle-case target of `ZhuVermaAnDescent10`) —
discharge the three reindexing predicates of `ZhuVermaAnDescent8`, making
`leftDescends_holds`/`rightDescends_holds` unconditional and `An.lActU`/`An.rActU` the unconditional
descended `A_n(𝒱)` bimodule actions, with the `n = 0` Zhu anchors `An.lActU_zero_mk`/`An.rActU_zero_mk`.

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* **`iterate_mem_grading`** — the acting iterate `u₍ᵢ₋₂₎v` is homogeneous of grade `M+P-(i-2)-1`
  (VA1, `smul_mem_grading`); `iterateGrade` is its integer grade.
* **`LeftGenTowerEq_holds_of_homogIterate` / `RightGenTowerEq_holds_of_homogIterate`** — the routing
  of the full `∀-args` `O(𝒱)`-generator predicates through the single homogeneous-acting-vector tower
  decomposition `(L-hom)`/`(R-hom)`, via the Descent11 per-iterate criteria + `iterate_mem_grading`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`):

  #print axioms VOA.iterate_mem_grading
  #print axioms VOA.LeftGenTowerEq_holds_of_homogIterate
  #print axioms VOA.RightGenTowerEq_holds_of_homogIterate
-/
