/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Final
import VOA.Modules.ZhuVermaAnArchMUcross
import VOA.Modules.ZhuVermaAnArchHingeCollapse

/-!
# Dong–Jiang `u_p` well-definedness — the **cross closure** `AnmCrossClosure`, via DJ Lemma 2.8.

This file closes the **cross-level** half of the `M(U)` graded-action crux, exactly as Dong–Jiang
prove it in the construction of `M(U)` (Dong–Jiang, *Bimodules associated to vertex operator
algebras*, Math. Z. 259 (2008) 799–826, `arXiv:math/0601626`, the `u_p` well-definedness, PDF lines
2074–2106).

## DJ's argument (NOT the cross-circle Vandermonde)

DJ define the loop modes `u_p : M(U)(n) → M(U)(n − wt u − p − 1)` by
`u_p(v ⊗ w) = (u ∗^{wt u−p−1+n}_{m,n} v) ⊗ w`, and prove well-definedness in two steps:

* **(A) Carrying the relations.**  If `v ∈ O_{n,m}(V)` then `u ∗^{n'}_{m,n} v ∈ O_{n',m}(V)`
  (`n' = wt u − p − 1 + n`), *"By Lemma 2.8"*.
* **(B) Right `A_m`-balance.**  `u ∗ (v ∗ a) = (u ∗ v) ∗ a`, the bimodule composition.

The repo's `AnmCrossClosure W n` is DJ's case (source level `0`, target level `n`, `m = 0`):

  `∀ a, ∀ g ∈ O_{0,0}(V), a ∗^n_{0,0} g ∈ O_{n,0}(V)`,

i.e. the **LEFT inclusion of Lemma 2.8** at `(n, m, p) = (n, 0, 0)` (where `∗^n_{0,0} = ∗^n_0 =
anmRight W n 0`, `anmGen_eq_anmRight`).  DJ's proof of Lemma 2.8 is *pure associativity*: it carries
the level-`0` ideal `O_{0,0}` to level `n` through the reassociation chain, discharging each bracket
into `O` via the `u = 1` associator defect — **no cross-circle Vandermonde, no inverted binomial
matrix, no per-generator residue collapse**.  That entire Vandermonde-free chain is already built
green and unconditional in this repo:

* the `u = 1` associator-defect step  →  `bareAssoc_mem_OnmFull` (`ZhuVermaAnArchDJ27`);
* the reassociation / level-mixing branch  →  `leftO'''_unconditional` (`ZhuVermaAnArchDJ28Final`),
  with the inner right-inclusion coupling discharged unconditionally;
* the assembled LEFT inclusion  →  `anmGen_OnmFull_left_of_leftGrading` (`ZhuVermaAnArchDJ28Final`),
  modulo the single residual `LeftGradingResidual W n m p` (the `O'_{p,m}` grading branch's
  right-slot absorption).

## What this file proves

`anmCrossClosure_of_collapse W n hcol : AnmCrossClosure W n`, depending only on the level-`0`
collapse `hcol : OnmCollapses W n` (`OnmFull W n 0 ≤ Onm W n 0`, the *same* collapse the right-module
half consumes, reduced by `onmFull_le_Onm_of_gens` to the two into-`O'` generator families — engine-
verified TRUE on the free boson, NOT a cross-circle Vandermonde).

The residual `LeftGradingResidual W n 0 0` that DJ's left inclusion carries is **discharged here at
`(n, 0, 0)`**: its single field `absorb a c : anmGen W n 0 0 a (anmLgen W 0 0 c) ∈ OnmFull W n 0` is,
after `anmGen_eq_anmRight`, exactly the already-proven `anmRight_zero_crossL_mem_Onm`
(`ZhuVermaAnArchMUcross`, lifted by `Onm_le_OnmFull`).  So the cross closure carries **no** open
residual beyond the shared collapse `OnmCollapses W n`.

No `sorry`, no `native_decide`, no `pbw` (DJ's `u_p` well-definedness is PBW-free; PBW enters DJ only
in the algebra `A_n(V)` Construction A and the `M(U)(n) ≅ A_{n,0} ⊗ U` identification, not here).
-/

universe u

namespace VOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The `(n, 0, 0)` instance of `LeftGradingResidual` — discharged, NOT carried.**

`LeftGradingResidual W n 0 0` has the single field
`absorb : ∀ a c, anmGen W n 0 0 a (anmLgen W 0 0 c) ∈ OnmFull W n 0`.  At `m = p = 0` the general
product `anmGen W n 0 0` *is* the repo right action `anmRight W n 0` (`anmGen_eq_anmRight`), so the
absorption reads `anmRight W n 0 a (anmLgen W 0 0 c) ∈ OnmFull W n 0` — which is the proven
`anmRight_zero_crossL_mem_Onm` (DJ Lemma 2.5 / total-derivative grading absorption, level `0`),
lifted from `Onm` to `OnmFull` by `Onm_le_OnmFull`.

This is the precise observation in the ReadDJ plan (Step 2): the *general*-`(n, m, p)` grading
absorption is open, but the *only* instance the `M(U)` `𝒱`-action consumes — the cross instance at
`(n, 0, 0)` — is a closed term. -/
theorem leftGradingResidual_zero_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    LeftGradingResidual W n 0 0 where
  absorb a c := by
    rw [anmGen_eq_anmRight]
    exact Onm_le_OnmFull W n 0 (anmRight_zero_crossL_mem_Onm W n a c)

/-- **DJ Lemma 2.8 LEFT inclusion at `(n, 0, 0)`, into the FULL ideal.**

`∀ g ∈ OnmFull W 0 0, anmRight W n 0 a g ∈ OnmFull W n 0`.  This is the verbatim level-carrying step
of DJ's `u_p` well-definedness (*"By Lemma 2.8, `u ∗^{…}_{m,n} v ∈ … ⊆ O_{…,m}(V)`"*), specialized to
source level `0`, target level `n`, `m = 0`.  Obtained from the Vandermonde-free assembled left
inclusion `anmGen_OnmFull_left_of_leftGrading` (DJ's associativity chain) with its carried residual
`LeftGradingResidual W n 0 0` discharged by `leftGradingResidual_zero_zero`, then rewritten through
`anmGen W n 0 0 = anmRight W n 0`. -/
theorem anmRight_zero_OnmFull_cross (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a : 𝒱) :
    ∀ g ∈ OnmFull W 0 0, anmRight W n 0 a g ∈ OnmFull W n 0 := by
  intro g hg
  have h := anmGen_OnmFull_left_of_leftGrading W n 0 0 a
    (leftGradingResidual_zero_zero W n) g hg
  rwa [anmGen_eq_anmRight] at h

/-- **The cross closure `AnmCrossClosure W n`, via DJ's `u_p` well-definedness.**

`∀ a, ∀ g ∈ Onm W 0 0, anmRight W n 0 a g ∈ Onm W n 0` — the well-definedness of the `M(U)` `𝒱`-action
on the level-`0` relations, carried to level `n`.  Following DJ (the across-levels associativity
argument, NOT the cross-circle Vandermonde):

* lift `g ∈ Onm W 0 0` to `OnmFull W 0 0` (`Onm_le_OnmFull`);
* apply the proven Vandermonde-free LEFT inclusion `anmRight_zero_OnmFull_cross`, landing in
  `OnmFull W n 0`;
* collapse `OnmFull W n 0` to `Onm W n 0` via the (shared) collapse `hcol : OnmCollapses W n`.

The only input beyond the closed DJ-2.8 left inclusion is the collapse `OnmCollapses W n`, which is
exactly the same collapse the right-module half (`AnmRightModule`) consumes — reduced by
`onmFull_le_Onm_of_gens` to the two into-`O'` generator families (`assocDefect`, `levelMix`), NOT a
cross-circle Vandermonde. -/
theorem anmCrossClosure_of_collapse (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcol : OnmCollapses W n) :
    AnmCrossClosure W n := by
  intro a g hg
  have h : anmRight W n 0 a g ∈ OnmFull W n 0 :=
    anmRight_zero_OnmFull_cross W n a g (Onm_le_OnmFull W 0 0 hg)
  exact hcol h

end VOA
