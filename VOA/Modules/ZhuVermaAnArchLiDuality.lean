/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The annihilator-stability duality — Li's Lemma 2.16 (the logical core of the Li route).

Haisheng Li ("Regular representations and `A_n(V)`-`A_m(V)` bimodules", arXiv 2205.05481, 2022) proves
the Dong–Jiang cross-level closure INTO THE PARTIAL IDEAL `O'` (= the repo's `Onm`) — resolving what the
combinatorial DJ iterate leaves circular — by a NON-LOCAL, module-theoretic argument: the dual of the
`O'`-quotient `A^†_{n,m}(W) = W/O'_{n,m}(W)` is identified with a vacuum space of the regular representation
`D^{(-1)}(W)`, hence is a module; by duality, `O'_{n,m}` is action-stable, i.e. the closure holds.

This file proves the abstract linear-algebra core of that argument — **Li Lemma 2.16 / 2.14** (the direction
that yields the primal closure from the dual): for a ℂ-linear `ψ : M → M` and subspaces `p, q ⊆ M`, if
`p` is **weak-* closed** (`p.dualAnnihilator.dualCoannihilator ≤ p`) and the transpose `ψ*` maps the
annihilator `Ann p` into `Ann q`, then `ψ` maps `q` into `p`.

Applied to the repo (`ψ = a ∗̄ⁿ_0 (·)`, `q = O(𝒱) = Onm 0 0`, `p = Onm n 0`), this reduces the cross-level
closure `CrossCircCore` to (a) `Onm n 0` weak-* closed (a GRADED finite-dim fact, per weight-space) and
(b) the DUAL condition `ψ*(Ann (Onm n 0)) ⊆ Ann (Onm 0 0)` — which Li supplies from the regular
representation (`(A^†_{n,0})* = Ω_{0,n}(D^{(-1)})` is an `A_0`-module, and `ψ*` a module map).

This is **step 5** of the Li-route roadmap.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
H. Li, arXiv 2205.05481, Lemmas 2.14/2.16, Thm 3.17; Dong–Jiang math/0601626 §2/§4; FHL.
-/

namespace VOA

open Submodule LinearMap

universe u

/-- **Li Lemma 2.16 (the closure direction).**  For `ψ : M →ₗ[ℂ] M` and subspaces `p q : Submodule ℂ M`,
if `p` is weak-* closed (`p.dualAnnihilator.dualCoannihilator ≤ p`) and the transpose `ψ.dualMap` carries
the annihilator `p.dualAnnihilator` into `q.dualAnnihilator`, then `ψ` maps `q` into `p`
(`∀ x ∈ q, ψ x ∈ p`).  The abstract heart of Li's module-theoretic cross-level closure: a primal
containment recovered from a dual (module) containment.  No finite-dimensionality is assumed — only the
weak-* closedness of the target `p` (which for the graded restricted dual holds per finite-dim
weight-space). -/
theorem mapsTo_of_dualMap_annihilator {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (ψ : M →ₗ[R] M) (p q : Submodule R M)
    (hclosed : p.dualAnnihilator.dualCoannihilator ≤ p)
    (hdual : ∀ f ∈ p.dualAnnihilator, ψ.dualMap f ∈ q.dualAnnihilator) :
    ∀ x ∈ q, ψ x ∈ p := by
  intro x hx
  apply hclosed
  rw [Submodule.mem_dualCoannihilator]
  intro f hf
  have hfq : ψ.dualMap f ∈ q.dualAnnihilator := hdual f hf
  rw [Submodule.mem_dualAnnihilator] at hfq
  have := hfq x hx
  rwa [LinearMap.dualMap_apply] at this

/-- **Closure form** — `ψ` maps the submodule `q` into `p` as `q ≤ p.comap ψ`.  Convenience repackaging
of `mapsTo_of_dualMap_annihilator` for feeding submodule-level closure statements (e.g. `Onm`-membership
of `a ∗̄ⁿ_0 g` for `g ∈ O(𝒱)`). -/
theorem le_comap_of_dualMap_annihilator {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (ψ : M →ₗ[R] M) (p q : Submodule R M)
    (hclosed : p.dualAnnihilator.dualCoannihilator ≤ p)
    (hdual : ∀ f ∈ p.dualAnnihilator, ψ.dualMap f ∈ q.dualAnnihilator) :
    q ≤ p.comap ψ := fun x hx => mapsTo_of_dualMap_annihilator ψ p q hclosed hdual x hx

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.mapsTo_of_dualMap_annihilator
  #print axioms VOA.le_comap_of_dualMap_annihilator
-/
