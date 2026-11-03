/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent16
import VOA.Modules.ZhuRingInstance

/-!
# The unconditional `n = 0` `A_0(𝒱)` bimodule actions (the genuine Zhu-ring bottom rung).

This file continues `Modules.ZhuVermaAnDescent16`.  It assembles the `A_n(𝒱)` bimodule actions
**unconditionally at `n = 0`** — with NO hypothesis whatsoever — and confirms that the descended
actions are exactly the Zhu-ring multiplication on `A(𝒱) = A_0(𝒱)`.

## Why `n = 0` is unconditional (and the honest scope vs. the parametric `An.lActU`/`An.rActU`)

The parametric descended actions `An.lActU`/`An.rActU` (`ZhuVermaAnDescent8`) and the bundled
`An.lActU'`/`An.rActU'` (`ZhuVermaAnDescent14`) are conditional on the three depth-`n` FZ
tower-collapse predicates — `LeftGenTowerEq_holds`/`RightGenTowerEq_holds` (the `gen_mem`
memberships `O(𝒱) *ₙ 𝒱 ⊆ Oₙ` / `𝒱 *ₙ O(𝒱) ⊆ Oₙ`) and `RightCircTowerEq_holds` (the
`RightDescends.on_mem` circle decomposition).  For `n ≥ 1` those three are the genuine Dong–Li–Mason
iterate-collapse content (the `i`-dependent diagonal-shift Vandermonde isolated as the two scalar
cores in `ZhuVermaAnDescent16`), NOT mechanical lifts; they are left there as PRECISE stated targets,
NOT `sorry`'d and NOT axiomatized.

At `n = 0`, however, the entire descent collapses to **Zhu's two-sided ideal theorem**, which is
proved unconditionally upstream (`ZhuRingInstance.zhuRingData_holds`, off `ZhuAssociator.associator_core`
+ `ZhuRightIdeal.right_ideal_core`, `pbw`-free).  Concretely:

* `Oₙ(𝒱)` at `n = 0` IS Zhu's `O(𝒱)`  (`On_zero_eq_O`, `ZhuVermaAnDescent15`);
* both FZ products at `n = 0` ARE the Zhu product `zhuMul`  (`leftProd_zero`/`rightProd_zero`);
* the four descent memberships (`LeftDescends`/`RightDescends` fields) are then exactly the two-sided
  ideal facts `ZhuRingData.left_ideal` (`O *ₙ 𝒱 ⊆ O`, `𝒱 *ₙ O ⊆ O` in the left/right `on_mem`
  resp. left `gen_mem` slot via the Zhu product) and `ZhuRingData.right_ideal` (the right `gen_mem`
  slot), with NO circle tower decomposition needed at the bottom rung.

So at `n = 0` we get the descent structures `LeftDescends W 0` / `RightDescends W 0` **hypothesis-free**,
hence the unconditional bimodule actions, and the bottom-rung Zhu-product reduction.

## What this file proves (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `O_two_sided` — `zhuRingData_holds`, re-exposed in the Descent namespace (the genuine two-sided
  ideal `O(𝒱)`, Zhu Thm 2.1.1/2.1.2, unconditional);
* **`leftDescends_zero_uncond`** / **`rightDescends_zero_uncond`** — the `n = 0` descent structures,
  built DIRECTLY from the `ZhuRingData` two-sided-ideal fields (no hypothesis);
* **`An.lActU_uncond`** / **`An.rActU_uncond`** — the unconditional `n = 0` descended `A(𝒱)`-bimodule
  actions on `A_0(𝒱)`, with the representative evaluations `An.lActU_uncond_mk`/`An.rActU_uncond_mk`;
* **`An.lActU_uncond_zhuMul`** / **`An.rActU_uncond_zhuMul`** — the `n = 0` reduction to the Zhu
  product: `[a]·[x] = [a * x]`, `[x]·[a] = [x * a]` (the bimodule actions ARE Zhu-ring multiplication
  on `A(𝒱)` at the bottom rung).

Note: the bundled `AnBimoduleInputs W n` (`ZhuVermaAnDescent14`) carries the `RightCircTowerEq`
*circle*-decomposition shape as one of its three fields, which the FZ tower form does not free even
at `n = 0`; we therefore route the unconditional `n = 0` actions through the direct descent
structures `leftDescends_zero_uncond`/`rightDescends_zero_uncond` (the Zhu two-sided ideal),
bypassing the circle-tower field entirely.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu Thm 2.1.1/2.1.2; Frenkel–Zhu Lemma 2.1.1/2.1.2; Dong–Li–Mason.
-/

open scoped BigOperators
open Finset

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The genuine two-sided ideal `O(𝒱)` (Zhu Thm 2.1.1/2.1.2), unconditional. -/

/-- **`O(𝒱)` is a two-sided `*`-ideal** (and `*` is associative mod `O(𝒱)`): Zhu Thm 2.1.1/2.1.2,
unconditional (`ZhuRingInstance.zhuRingData_holds`, off `associator_core` + `right_ideal_core`,
`pbw`-free).  Re-exposed here as the bottom-rung engine of the `n = 0` bimodule descent. -/
theorem O_two_sided (W : VertexOperatorAlgebra 𝒱) : ZhuRingData W := zhuRingData_holds W

/-! ## The `n = 0` descent structures, built hypothesis-free from the two-sided ideal. -/

/-- **`LeftDescends W 0`, unconditional.**  At `n = 0`, `leftProd W 0 = zhuMul` (`leftProd_zero`) and
`Oₙ(𝒱) = O(𝒱)` (`On_zero_eq_O`), so the two `LeftDescends` fields become Zhu's two-sided-ideal facts:
the `gen_mem` field `O(𝒱) *₀ 𝒱 ⊆ O₀` is the left ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)` (`ZhuRingData.left_ideal`),
and the `on_mem` field `𝒱 *₀ O₀ ⊆ O₀` is the right ideal `𝒱 * O(𝒱) ⊆ O(𝒱)`
(`ZhuRingData.right_ideal`).  No tower decomposition, no hypothesis. -/
theorem leftDescends_zero_uncond (W : VertexOperatorAlgebra 𝒱) : LeftDescends W 0 where
  gen_mem := by
    intro g hg b
    rw [On_zero_eq_O, leftProd_zero]
    exact (O_two_sided W).left_ideal hg b
  on_mem := by
    intro a x hx
    rw [On_zero_eq_O] at hx ⊢
    rw [leftProd_zero]
    exact (O_two_sided W).right_ideal a hx

/-- **`RightDescends W 0`, unconditional.**  At `n = 0`, `rightProd W 0 = zhuMul` (`rightProd_zero`)
and `Oₙ(𝒱) = O(𝒱)` (`On_zero_eq_O`), so the two `RightDescends` fields become Zhu's two-sided-ideal
facts: the `on_mem` field `O₀ *₀ 𝒱 ⊆ O₀` is the left ideal `O(𝒱) * 𝒱 ⊆ O(𝒱)`
(`ZhuRingData.left_ideal`), and the `gen_mem` field `𝒱 *₀ O(𝒱) ⊆ O₀` is the right ideal
`𝒱 * O(𝒱) ⊆ O(𝒱)` (`ZhuRingData.right_ideal`).  This is the bottom-rung counterpart that
`ZhuVermaAnDescent15`'s `leftDescends_zero` could NOT supply for the right side (it additionally
needed the circle predicate `RightCircTowerEq W 0`); routing through the Zhu two-sided ideal
bypasses the FZ circle tower shape entirely at `n = 0`. -/
theorem rightDescends_zero_uncond (W : VertexOperatorAlgebra 𝒱) : RightDescends W 0 where
  on_mem := by
    intro x hx a
    rw [On_zero_eq_O] at hx ⊢
    rw [rightProd_zero]
    exact (O_two_sided W).left_ideal hx a
  gen_mem := by
    intro x g hg
    rw [On_zero_eq_O, rightProd_zero]
    exact (O_two_sided W).right_ideal x hg

/-! ## The unconditional `n = 0` descended bimodule actions. -/

/-- **The unconditional `n = 0` left action** `A(𝒱) →ₗ A_0(𝒱) →ₗ A_0(𝒱)`, `([a], [x]) ↦ [a *₀ x]`,
from the hypothesis-free `leftDescends_zero_uncond`.  No tower predicate, no hypothesis. -/
noncomputable def An.lActU_uncond (W : VertexOperatorAlgebra 𝒱) :
    A W →ₗ[ℂ] An W 0 →ₗ[ℂ] An W 0 :=
  An.lAct W 0 (leftDescends_zero_uncond W)

/-- **The unconditional `n = 0` right action** `A_0(𝒱) →ₗ A(𝒱) →ₗ A_0(𝒱)`, `([x], [a]) ↦ [x *₀ a]`,
from the hypothesis-free `rightDescends_zero_uncond`.  No tower predicate, no hypothesis. -/
noncomputable def An.rActU_uncond (W : VertexOperatorAlgebra 𝒱) :
    An W 0 →ₗ[ℂ] A W →ₗ[ℂ] An W 0 :=
  An.rAct W 0 (rightDescends_zero_uncond W)

/-- The unconditional `n = 0` left action on representatives: `[a] · [x] = [a *₀ x]`. -/
@[simp] theorem An.lActU_uncond_mk (W : VertexOperatorAlgebra 𝒱) (a x : 𝒱) :
    An.lActU_uncond W (mk W a) (mkAn W 0 x) = mkAn W 0 (leftProd W 0 a x) :=
  An.lAct_mk W 0 (leftDescends_zero_uncond W) a x

/-- The unconditional `n = 0` right action on representatives: `[x] · [a] = [x *₀ a]`. -/
@[simp] theorem An.rActU_uncond_mk (W : VertexOperatorAlgebra 𝒱) (x a : 𝒱) :
    An.rActU_uncond W (mkAn W 0 x) (mk W a) = mkAn W 0 (rightProd W 0 x a) :=
  An.rAct_mk W 0 (rightDescends_zero_uncond W) x a

/-! ## The `n = 0` reduction to the Zhu product (the bottom-rung correctness anchor). -/

/-- **The unconditional `n = 0` left action IS Zhu-ring multiplication.**  `[a] · [x] = [a * x]` —
the descended left action on `A_0(𝒱)` reduces to the Zhu product `zhuMul` at the bottom rung
(`leftProd W 0 = zhuMul`).  Pins the construction to the existing associative Zhu-ring multiplication
on `A(𝒱)` (`ZhuRingInstance.instRingA`). -/
@[simp] theorem An.lActU_uncond_zhuMul (W : VertexOperatorAlgebra 𝒱) (a x : 𝒱) :
    An.lActU_uncond W (mk W a) (mkAn W 0 x) = mkAn W 0 (zhuMul W a x) :=
  An.lAct_zero_mk W (leftDescends_zero_uncond W) a x

/-- **The unconditional `n = 0` right action IS Zhu-ring multiplication.**  `[x] · [a] = [x * a]`
(`rightProd W 0 = zhuMul`). -/
@[simp] theorem An.rActU_uncond_zhuMul (W : VertexOperatorAlgebra 𝒱) (x a : 𝒱) :
    An.rActU_uncond W (mkAn W 0 x) (mk W a) = mkAn W 0 (zhuMul W x a) :=
  An.rAct_zero_mk W (rightDescends_zero_uncond W) x a

/-!
## What this proves and the honest `n ≥ 1` scope

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

* **`O_two_sided`** — Zhu's two-sided ideal `O(𝒱)` (Thm 2.1.1/2.1.2), unconditional.
* **`leftDescends_zero_uncond`** / **`rightDescends_zero_uncond`** — the `n = 0` descent structures
  `LeftDescends W 0` / `RightDescends W 0`, built hypothesis-free from the two-sided-ideal fields
  (`On_zero_eq_O` + `leftProd_zero`/`rightProd_zero` collapse the FZ products to `zhuMul`).
* **`An.lActU_uncond`** / **`An.rActU_uncond`** — the unconditional `n = 0` descended bimodule actions
  on `A_0(𝒱)`, with `An.lActU_uncond_mk`/`An.rActU_uncond_mk` (representative evaluations).
* **`An.lActU_uncond_zhuMul`** / **`An.rActU_uncond_zhuMul`** — the bottom-rung reduction: the
  descended actions ARE the Zhu-ring multiplication `[a]·[x] = [a*x]`, `[x]·[a] = [x*a]`.

These complete the `n = 0` case — the unconditional bimodule actions and the n=0
reduction to the Zhu product — through the genuine Zhu two-sided ideal, NOT through any of the three
still-open depth-`n` tower-collapse predicates.

### Honest `n ≥ 1` scope (matching the `ZhuVermaAnDescent15`/`16` caveats)

The general-`n` unconditional actions still require the three depth-`n` FZ predicates:
* `LeftGenTowerEq_holds` (`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`) and `RightGenTowerEq_holds` (`𝒱 *ₙ O(𝒱) ⊆ Oₙ`) — the
  `gen_mem` fields; reduced in `ZhuVermaAnDescent15` to the homogeneous targets `(L-hom)`/`(R-hom)`;
* `RightCircTowerEq_holds` — the `RightDescends.on_mem` circle decomposition; reduced in
  `ZhuVermaAnDescent16` to the two scalar cores `(U-core)`/`(V-core)` (the `i`-dependent
  diagonal-shift Vandermonde).

For `n ≥ 1` these are the genuine Dong–Li–Mason iterate-collapse combinatorics, NOT mechanical lifts
of the `n = 0` ideal proof (the `O(𝒱)`-generator's mode `i-2` is `n`-independent, so the naive
reassembly lands in `O(𝒱) ⊄ Oₙ` for `n ≥ 1`; cf. `ZhuVermaAnDescent4` lines 867–871 and the
`ZhuVermaAnDescent15` caveat).  They are left as the PRECISE stated targets in `15`/`16`, NOT
`sorry`'d and NOT axiomatized.  Supplying them feeds `AnBimoduleInputs` (`ZhuVermaAnDescent14`) and
makes `An.lActU'`/`An.rActU'` unconditional at all `n`; the `n = 0` instances of all three predicates
are exactly the Zhu two-sided-ideal facts used here.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.O_two_sided
  #print axioms VOA.leftDescends_zero_uncond
  #print axioms VOA.rightDescends_zero_uncond
  #print axioms VOA.An.lActU_uncond
  #print axioms VOA.An.rActU_uncond
  #print axioms VOA.An.lActU_uncond_mk
  #print axioms VOA.An.rActU_uncond_mk
  #print axioms VOA.An.lActU_uncond_zhuMul
  #print axioms VOA.An.rActU_uncond_zhuMul
-/
