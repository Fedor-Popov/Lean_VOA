/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnDescent13

/-!
# The `A_n(𝒱)` bimodule-action ASSEMBLY: wiring the three reduced targets into the
unconditional `LeftDescends`/`RightDescends` and the bimodule actions `An.lActU'`/`An.rActU'`.

This file is the *assembly point* of the `A_n(𝒱)` bimodule descent.  Every piece of plumbing
between the genuine FZ memberships and the final descended `A(𝒱)`-bimodule actions on `A_n(𝒱)` is
wired here once, so that the moment the genuine combinatorial cores land, the unconditional actions
follow by a single application — no plumbing is re-derived downstream.

## The three GENUINE reduced targets

By the proved reductions (`ZhuVermaAnDescent8`/`10`/`13`), the entire bimodule descent rests on
exactly three membership/decomposition statements:

* **(L-mem)**  `∀ u v b, leftProd W n ((L₋₁u+L₀u)*v) b ∈ Oₙ(𝒱)`   (`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`, the
  `LeftDescends.gen_mem` field).  Via `LeftGenTowerEq_holds_of_mem` (`ZhuVermaAnDescent13`) this is the
  exact content of the left `gen_mem` tower-decomposition predicate, established by
  `TowerDecomp_iff_mem_On` to be plain `Oₙ`-membership.

* **(R-mem)**  `∀ x u v, rightProd W n x ((L₋₁u+L₀u)*v) ∈ Oₙ(𝒱)`   (`𝒱 *ₙ O(𝒱) ⊆ Oₙ`, the
  `RightDescends.gen_mem` field).  Via `RightGenTowerEq_holds_of_mem` (`ZhuVermaAnDescent13`).

* **(circ)**  `RightCircTowerEq W n M P c d a` for all homogeneous `c ∈ 𝒱_M`, `d ∈ 𝒱_P`,
  `a ∈ 𝒱_K` (the `RightDescends.on_mem` field, via `rightProd_On_mem_On_of_towerEq`,
  `ZhuVermaAnDescent8`).

The fourth membership — `LeftDescends.on_mem` (`𝒱 *ₙ Oₙ ⊆ Oₙ`) — is ALREADY unconditional
(`leftProd_On_mem_On`, `ZhuVermaAnDescent4`).

## What this file assembles (axiom-clean)

* `AnBimoduleInputs W n` — a `Prop`-structure bundling exactly (L-mem)/(R-mem)/(circ): the complete,
  minimal set of genuine reduced targets the bimodule descent needs.
* `AnBimoduleInputs.toLeftDescends` / `AnBimoduleInputs.toRightDescends` — the bundled inputs produce
  the two descent structures (wiring the already-unconditional `leftProd_On_mem_On` /
  `rightProd_On_mem_On_of_towerEq` for the `on_mem` fields).
* `leftDescends_of_genMem` / `rightDescends_of_circAndGenMem` — the direct constructions of
  `LeftDescends`/`RightDescends` from the individual reduced targets (the membership route, NOT the
  abstract `*TowerEq` predicates).
* **`An.lActU'` / `An.rActU'`** — the descended `A(𝒱)`-bimodule actions on `A_n(𝒱)` from the bundled
  inputs, with the representative-level evaluations `An.lActU'_mk`/`An.rActU'_mk` and the **`n = 0`
  Zhu anchors** `An.lActU'_zero_mk`/`An.rActU'_zero_mk` (the descended actions reduce to Zhu
  multiplication at the bottom rung).

## Status of the three reduced targets

These three are genuine VOA memberships / a finsum-regrouping equality — NOT axioms, NOT `sorry`'d.
They are the depth-`n` lifts of the `n = 0` two-sided-ideal cores `gen_mem_O` (`ZhuModule`),
`ZhuHR.right_ideal_core` (`ZhuRightIdeal`), and the `n = 0` associator route
`ZhuAssociator.assoc_eq`.  Their combinatorial engine (`ZhuRes.gen_vandermonde`/`gen_jsum`,
`Pres_mem_On`, `coeffSn_eq_coeffPn`) is fully proved.  Until they land, `AnBimoduleInputs` is the
single hypothesis carrying them, and the actions are conditional on it alone — exactly as the
parametric `An.lActU`/`An.rActU` (`ZhuVermaAnDescent8`) were conditional on the abstract `*TowerEq`
predicates, but here expressed at the *membership* level (the honest reduced targets) rather than the
abstract reindexing-predicate level.

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

/-! ## The descent structures from the individual reduced targets (the membership route). -/

/-- **`LeftDescends W n` from (L-mem).**  The `gen_mem` field is the genuine FZ membership
`O(𝒱) *ₙ 𝒱 ⊆ Oₙ`, fed in on circle/`O(𝒱)`-generators via `O_eq_span` + `leftProdFstL` linearity; the
`on_mem` field is the already-unconditional `leftProd_On_mem_On` (`ZhuVermaAnDescent4`).  This is the
membership-level analog of `leftDescends_of_towerEq` (`ZhuVermaAnDescent8`), routing (L-mem) through
`LeftGenTowerEq_holds_of_mem` (`ZhuVermaAnDescent13`). -/
theorem leftDescends_of_genMem (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Lmem : ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n) :
    LeftDescends W n :=
  leftDescends_holds W n (LeftGenTowerEq_holds_of_mem W n Lmem)

/-- **`RightDescends W n` from (circ) + (R-mem).**  The `on_mem` field is the circle-generator tower
decomposition `RightCircTowerEq` carried into `Oₙ` by `Pres_mem_On`
(`rightProd_On_mem_On_of_towerEq`, `ZhuVermaAnDescent8`); the `gen_mem` field is the genuine FZ
membership `𝒱 *ₙ O(𝒱) ⊆ Oₙ` (R-mem), routed through `RightGenTowerEq_holds_of_mem`
(`ZhuVermaAnDescent13`).  Membership-level analog of `rightDescends_of_towerEq`. -/
theorem rightDescends_of_circAndGenMem (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
      a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a)
    (Rmem : ∀ x u v : 𝒱, rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n) :
    RightDescends W n :=
  rightDescends_holds W n Htow (RightGenTowerEq_holds_of_mem W n Rmem)

/-! ## The minimal bundled inputs `AnBimoduleInputs`. -/

/-- **The complete, minimal set of genuine reduced targets** for the `A_n(𝒱)` bimodule descent,
bundled as a `Prop`-structure.  Holding `AnBimoduleInputs W n` is equivalent to supplying the three
genuine reduced targets (L-mem)/(circ)/(R-mem); the fourth membership (`LeftDescends.on_mem`) is
already unconditional and so is NOT a field. -/
structure AnBimoduleInputs (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop where
  /-- **(L-mem)** `O(𝒱) *ₙ 𝒱 ⊆ Oₙ`: the left `gen_mem` FZ membership for `O(𝒱)`-base generators. -/
  Lmem : ∀ u v b : 𝒱, leftProd W n (zhuMul W (W.L (-1) u + W.L 0 u) v) b ∈ On W n
  /-- **(circ)** the right-product circle tower decomposition (the `RightDescends.on_mem` source). -/
  circTow : ∀ (M P K : ℕ) {c d a : 𝒱}, c ∈ W.grading (M : ℤ) → d ∈ W.grading (P : ℤ) →
    a ∈ W.grading (K : ℤ) → RightCircTowerEq W n M P c d a
  /-- **(R-mem)** `𝒱 *ₙ O(𝒱) ⊆ Oₙ`: the right `gen_mem` FZ membership for `O(𝒱)`-base generators. -/
  Rmem : ∀ x u v : 𝒱, rightProd W n x (zhuMul W (W.L (-1) u + W.L 0 u) v) ∈ On W n

/-- The bundled inputs yield `LeftDescends W n`. -/
theorem AnBimoduleInputs.toLeftDescends {W : VertexOperatorAlgebra 𝒱} {n : ℕ}
    (h : AnBimoduleInputs W n) : LeftDescends W n :=
  leftDescends_of_genMem W n h.Lmem

/-- The bundled inputs yield `RightDescends W n`. -/
theorem AnBimoduleInputs.toRightDescends {W : VertexOperatorAlgebra 𝒱} {n : ℕ}
    (h : AnBimoduleInputs W n) : RightDescends W n :=
  rightDescends_of_circAndGenMem W n h.circTow h.Rmem

/-! ## The descended bimodule actions from the bundled inputs. -/

/-- **The descended left action** `A(𝒱) →ₗ A_n(𝒱) →ₗ A_n(𝒱)`, `([a], [x]) ↦ [a *ₙ x]`, from the
bundled inputs `AnBimoduleInputs W n`. -/
noncomputable def An.lActU' (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (h : AnBimoduleInputs W n) :
    A W →ₗ[ℂ] An W n →ₗ[ℂ] An W n :=
  An.lAct W n h.toLeftDescends

/-- **The descended right action** `A_n(𝒱) →ₗ A(𝒱) →ₗ A_n(𝒱)`, `([x], [a]) ↦ [x *ₙ a]`, from the
bundled inputs `AnBimoduleInputs W n`. -/
noncomputable def An.rActU' (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (h : AnBimoduleInputs W n) :
    An W n →ₗ[ℂ] A W →ₗ[ℂ] An W n :=
  An.rAct W n h.toRightDescends

/-- The descended left action on representatives: `[a] · [x] = [a *ₙ x]`. -/
@[simp] theorem An.lActU'_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (h : AnBimoduleInputs W n)
    (a x : 𝒱) :
    An.lActU' W n h (mk W a) (mkAn W n x) = mkAn W n (leftProd W n a x) :=
  An.lAct_mk W n h.toLeftDescends a x

/-- The descended right action on representatives: `[x] · [a] = [x *ₙ a]`. -/
@[simp] theorem An.rActU'_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (h : AnBimoduleInputs W n)
    (x a : 𝒱) :
    An.rActU' W n h (mkAn W n x) (mk W a) = mkAn W n (rightProd W n x a) :=
  An.rAct_mk W n h.toRightDescends x a

/-! ## The `n = 0` Zhu anchors: the descended actions reduce to Zhu multiplication. -/

/-- **`n = 0` anchor (left):** the descended left action is the Zhu product `[a]·[x] = [a*x]`
(`leftProd W 0 = zhuMul`).  Confirms the bottom-rung reduction to the Zhu ring multiplication on
`A(𝒱)` (`ZhuRingInstance`). -/
@[simp] theorem An.lActU'_zero_mk (W : VertexOperatorAlgebra 𝒱) (h : AnBimoduleInputs W 0)
    (a x : 𝒱) :
    An.lActU' W 0 h (mk W a) (mkAn W 0 x) = mkAn W 0 (zhuMul W a x) :=
  An.lAct_zero_mk W h.toLeftDescends a x

/-- **`n = 0` anchor (right):** the descended right action is the Zhu product `[x]·[a] = [x*a]`
(`rightProd W 0 = zhuMul`). -/
@[simp] theorem An.rActU'_zero_mk (W : VertexOperatorAlgebra 𝒱) (h : AnBimoduleInputs W 0)
    (x a : 𝒱) :
    An.rActU' W 0 h (mkAn W 0 x) (mk W a) = mkAn W 0 (zhuMul W x a) :=
  An.rAct_zero_mk W h.toRightDescends x a

/-!
## What this proves and the PRECISE remaining targets (NOT `sorry`, NOT axiomatized)

Proved here (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* **`leftDescends_of_genMem`** — `LeftDescends W n` from the genuine left FZ membership (L-mem)
  (`on_mem` is the unconditional `leftProd_On_mem_On`).
* **`rightDescends_of_circAndGenMem`** — `RightDescends W n` from the circle tower decomposition
  (circ) and the genuine right FZ membership (R-mem).
* **`AnBimoduleInputs`** + `toLeftDescends`/`toRightDescends` — the minimal bundle of the three
  genuine reduced targets, producing both descent structures.
* **`An.lActU'`/`An.rActU'`** — the descended `A(𝒱)`-bimodule actions on `A_n(𝒱)` from the bundle,
  with `An.lActU'_mk`/`An.rActU'_mk` (representative evaluations) and the **`n = 0` Zhu anchors**
  `An.lActU'_zero_mk`/`An.rActU'_zero_mk`.

The bimodule descent is therefore wired end-to-end: any holder of `AnBimoduleInputs W n` gives the
unconditional actions.  The three fields of `AnBimoduleInputs` are the genuine remaining targets —
the depth-`n` FZ memberships (L-mem)/(R-mem) (lifts of `gen_mem_O`/`ZhuHR.right_ideal_core`) and the
circle tower decomposition (circ) (the depth-`n` `ZhuAssociator.assoc_eq` route, reduced in
`ZhuVermaAnDescent10` to the per-`(γ,μ)` scalar U-core/V-core `gen_vandermonde`/`gen_jsum`
collapse).  They are NOT axioms and NOT `sorry`'d; their combinatorial engine is fully proved.
Supplying any of them flips the corresponding field; supplying all three makes `An.lActU'`/`An.rActU'`
the unconditional descended `A_n(𝒱)` bimodule actions.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.leftDescends_of_genMem
  #print axioms VOA.rightDescends_of_circAndGenMem
  #print axioms VOA.AnBimoduleInputs.toLeftDescends
  #print axioms VOA.AnBimoduleInputs.toRightDescends
  #print axioms VOA.An.lActU'
  #print axioms VOA.An.rActU'
  #print axioms VOA.An.lActU'_mk
  #print axioms VOA.An.rActU'_mk
  #print axioms VOA.An.lActU'_zero_mk
  #print axioms VOA.An.rActU'_zero_mk
-/
