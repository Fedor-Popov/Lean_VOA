/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Character

/-!
# Li's regular representation `D^{(-1)}(𝒱)` — brick 1: the full-dual FHL adjoint `Y*_𝒱`.

To discharge `LiDualStable` (`ZhuVermaAnArchLiReduce`) — Haisheng Li's dual-module condition (arXiv
2205.05481, Thm 3.17), which is the Half-A keystone in dual form — we build Li's regular representation
`D^{(-1)}(𝒱) ⊂ 𝒱^*` and the duality `(A^†_{n,m})^* = Ω_{m,n}(D^{(-1)}(𝒱))`.

This file proves **brick 1**: the FHL (Frenkel–Huang–Lepowsky) adjoint vertex operator on the FULL dual
`Module.Dual ℂ 𝒱`.  For a homogeneous `u ∈ 𝒱` of weight `wt`, the adjoint mode `Y^*(u)_n : 𝒱^* → 𝒱^*`
is the transpose of the operator

  `adjOp W wt u n  :=  (-1)^wt · ∑_{j ≤ wt} (1/j!) · (L₁ʲu)₍2wt-n-2-j₎`   (on `𝒱`),

i.e. `(Y^*(u)_n f)(x) = (-1)^wt ∑_j (1/j!) · f((L₁ʲu)₍2wt-n-2-j₎ x)`.  This is the mode expansion of the
FHL adjoint `⟨Y^*(u,z)f, x⟩ = ⟨f, Y(e^{zL(1)}(-z^{-2})^{L(0)}u, z^{-1})x⟩` — the same `dualCompMap`
operator the repo's contragredient (`ContragredientAction`) uses on the graded restricted dual, here on
the FULL dual (needed so that `onmWeakClosed_holds`'s over-`ℂ` double-annihilator applies).

Roadmap (Li §3): brick 1 = `adjOp`/`Yadj` (here); then the two commuting actions `Y^L, Y^R` and the
`V⊗V`-module `D^{(-1)}(𝒱)` (Thm 3.2), the vacuum spaces `Ω_{m,n}` (Def 3.4), Prop 3.5 (the truncation
characterization `(A^†_{n,m})^* = Ω_{m,n}`), Cor 3.8 / Thm 3.17 (module structure + duality), and finally
`LiDualStable`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
H. Li, arXiv 2205.05481 (regular representations / `A_n(V)`-`A_m(V)` bimodules), §3, Def 3.1/Thm 3.2/
Def 3.4/Prop 3.5/Cor 3.8/Thm 3.17; FHL; repo `ContragredientAction.dualCompMap`.
-/

namespace VOA

open VertexOperatorAlgebra LinearMap

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The FHL adjoint operator on `𝒱`** for a homogeneous `u` of weight `wt`, mode `n`:
`adjOp W wt u n = (-1)^wt · ∑_{j ≤ wt} (1/j!) · (L₁ʲu)₍2wt-n-2-j₎`.  The operator whose transpose is
Li's regular-representation adjoint mode `Y^*(u)_n` on `𝒱^*`.  (Same shape as
`ContragredientAction.dualCompMap`'s `dualTargetOp`, on `𝒱`-as-a-`𝒱`-module with `Y_M = W.Y`, without
the graded projection — for the FULL dual.) -/
noncomputable def adjOp (W : VertexOperatorAlgebra 𝒱) (wt : ℤ) (u : 𝒱) (n : ℤ) : 𝒱 →ₗ[ℂ] 𝒱 :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • modeLinear (2 * wt - n - 2 - (j : ℤ)) (W.Y ((W.L 1 ^ j) u))

theorem adjOp_apply (W : VertexOperatorAlgebra 𝒱) (wt : ℤ) (u : 𝒱) (n : ℤ) (x : 𝒱) :
    adjOp W wt u n x
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
          ((j.factorial : ℂ)⁻¹) • modeLinear (2 * wt - n - 2 - (j : ℤ)) (W.Y ((W.L 1 ^ j) u)) x := by
  simp only [adjOp, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- **Li's regular-representation adjoint mode** `Y^*(u)_n : 𝒱^* → 𝒱^*` on the FULL dual — the transpose
of `adjOp` (precomposition): `(Yadj W wt u n f) x = f (adjOp W wt u n x)`. -/
noncomputable def Yadj (W : VertexOperatorAlgebra 𝒱) (wt : ℤ) (u : 𝒱) (n : ℤ) :
    Module.Dual ℂ 𝒱 →ₗ[ℂ] Module.Dual ℂ 𝒱 :=
  LinearMap.lcomp ℂ ℂ (adjOp W wt u n)

@[simp] theorem Yadj_apply (W : VertexOperatorAlgebra 𝒱) (wt : ℤ) (u : 𝒱) (n : ℤ)
    (f : Module.Dual ℂ 𝒱) (x : 𝒱) :
    Yadj W wt u n f x = f (adjOp W wt u n x) := rfl

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.adjOp
  #print axioms VOA.Yadj
-/
