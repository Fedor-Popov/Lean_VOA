/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Final
import VOA.Modules.ZhuVermaAnArchHingeCollapse

/-!
# Dong–Jiang **Lemma 2.8 "in particular" (right)** — the `u_p` right `A_0`-module closure.

This file closes the **right-module half** of the main theorem bottleneck `MUGradedAction`, namely

  `AnmRightModule W n  :=  ∀ g ∈ Onm W n 0, ∀ v, anmRight W n 0 g v ∈ Onm W n 0`
  (`ZhuVermaAnArchAnm`),

which is Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008)
799–826 (`math/0601626`), **Lemma 2.8 "in particular"**, the RIGHT inclusion
`O_{n,m} ∗ⁿ_m V ⊆ O_{n,m}` at `m = 0`:

  `O_{n,0}(𝒱) ∗ⁿ_0 𝒱 ⊆ O_{n,0}(𝒱)`,

i.e. the right `A_0(𝒱) = A(𝒱)`-action descends to `A_{n,0}(𝒱)`.  This is exactly the right
`A_m`-balance / well-definedness obligation for the loop modes `u_p` on `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U`
(DJ Prop 3.4); together with the cross-closure half it makes the `V`-action well defined.

## The proof is the proven Vandermonde-free DJ right inclusion, then the collapse

DJ proves the right inclusion `O_{n,p} ∗ⁿ_{m,p} V ⊆ O_{n,m}` (DJ display (2.2)) by **pure
reassociation** of the three-index products plus the `u = 1` associator defect
`(a ∗ⁿ_{p₁,p₂} b) ∗ⁿ_{m,p₁} c − a ∗ⁿ_{m,p₂} (b ∗^{p₂}_{m,p₁} c) ∈ O''_{n,m} ⊆ O_{n,m}` — **no**
cross-circle Vandermonde, **no** PBW.  This is already a fully unconditional term in this repo:

  `anmRight_OnmFull_unconditional W n m v : ∀ g ∈ OnmFull W n m, anmRight W n m g v ∈ OnmFull W n m`
  (`ZhuVermaAnArchDJ28Final`),

built from `anmGen_OnmFull_right_unconditional` (the three unconditional right generator branches
`anmRight_O'Circ_mem`/`anmRight_O''_mem`/`anmRight_O'''_mem`), with **no** `LeftGradingResidual` and
**no** `pbw`.

Hence `AnmRightModule W n` needs nothing beyond:
* lifting `g ∈ Onm W n 0` into the full ideal via the proven `Onm_le_OnmFull`;
* applying the proven unconditional right inclusion `anmRight_OnmFull_unconditional` (its output
  lands in `OnmFull W n 0`);
* collapsing `OnmFull W n 0 ≤ Onm W n 0`.

The collapse is carried as the named predicate `OnmCollapses W n` (`ZhuVermaAnArchHingeCollapse`),
which is the same `m = 0` collapse the cross-closure half consumes.  It is NOT an axiom and NOT
faked: `onmFull_le_Onm_of_gens` reduces it to the two into-`O'` generator families (`assocDefect`,
`levelMix`), the DJ Lemma 2.6/2.7 *into-`O'`* combinatorics, which are engine-supported on the
free boson and are emphatically **not** a cross-circle Vandermonde.

## Proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`; no `sorry`/`pbw`)

* `anmRightModule_of_collapse` — `OnmCollapses W n ⟹ AnmRightModule W n`, the right-module half of
  `MUGradedAction W n`, from the proven unconditional DJ 2.8 right inclusion plus the collapse.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 Lemma 2.8 ("in particular", right),
§3 Prop 3.4 (the `u_p` right `A_m`-balance).
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **DJ Lemma 2.8 "in particular" (right), `m = 0` — the `M(U)` right `A_0`-module closure.**

`AnmRightModule W n`: `∀ g ∈ Onm W n 0, ∀ v, anmRight W n 0 g v ∈ Onm W n 0`, i.e.
`O_{n,0}(𝒱) ∗ⁿ_0 𝒱 ⊆ O_{n,0}(𝒱)` — the right `A_0(𝒱)`-action descends to `A_{n,0}(𝒱)`.

The level-carrying / right reassociation content is the proven **unconditional** DJ 2.8 right
inclusion `anmRight_OnmFull_unconditional` (Vandermonde-free, PBW-free).  The only further input is
the `m = 0` collapse `OnmCollapses W n : OnmFull W n 0 ≤ Onm W n 0`, carried as a hypothesis (the
same collapse the cross-closure half consumes; reduced by `onmFull_le_Onm_of_gens` to the two
into-`O'` generator families). -/
theorem anmRightModule_of_collapse (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcol : OnmCollapses W n) :
    AnmRightModule W n := by
  intro g hg v
  -- Lift the partial-ideal hypothesis into the full DJ ideal.
  have hgF : g ∈ OnmFull W n 0 := Onm_le_OnmFull W n 0 hg
  -- DJ 2.8 right inclusion (unconditional): the right action lands back in the full ideal.
  have hF : anmRight W n 0 g v ∈ OnmFull W n 0 :=
    anmRight_OnmFull_unconditional W n 0 v g hgF
  -- Collapse `OnmFull W n 0 ≤ Onm W n 0` (the `m = 0` collapse `OnmCollapses W n`).
  exact hcol hF

end VOA
