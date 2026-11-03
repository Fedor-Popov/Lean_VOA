/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUBalancedBottom
import VOA.Modules.ZhuRingInstance

/-!
# The balanced bottom `M(U)(0) ≅ U` **as `A(𝒱)`-modules** (the genuine Dong–Jiang statement)

`ZhuVermaAnArchMUBalancedBottom` gave the balanced bottom `MUBalBottom W U = (A(𝒱) ⊗_ℂ U) ⧸ bottomBalancing`
and the `ℂ`-linear iso `muBalBottomEquiv : MUBalBottom ≅ U`.  For the Zhu bijection the bottom must recover
`U` **as an `A(𝒱)`-module**, not merely as a `ℂ`-space.  This file upgrades the R0 statement to `A(𝒱)`-
linear form, using the proved Zhu ring/algebra/module structures (`instRingA`, `instAlgebraA`, `moduleMh`).

The left `A(𝒱)`-action on the `ℂ`-tensor cover is `b • (a ⊗ u) = (b·a) ⊗ u` (`TensorProduct.smul_tmul'`);
on the lowest weight space `U = P_h` it is `moduleMh`'s action `b • u = ρ(b) u`.  The R0 action map
`bottomAct : A(𝒱) ⊗_ℂ U → U` is then **`A(𝒱)`-linear** — its `map_smul` is exactly the module axiom
`(b·a) • u = b • (a • u)` (`mul_smul`): `bottomAct(b • (a⊗u)) = ρ(b·a)u = ρ(b)(ρ(a)u) = b • bottomAct(a⊗u)`.

## Contents (axiom-clean, pbw-free; all inside one `section` with the proved `letI` instances)

* **`bottomActA P`** — the `A(𝒱)`-linear R0 action map (same underlying function as `MUConstruct.bottomAct`).
* **`bottomActA_surjective`** — surjective (`[𝟙] ⊗ u ↦ u`), inherited from `bottomAct_surjective`.
* **`MUBalBottomA P := (A(𝒱) ⊗_ℂ P_h) ⧸ ker (bottomActA P)`** — the balanced bottom as an `A(𝒱)`-module.
* **`muBalBottomEquivA P : MUBalBottomA P ≃ₗ[A(𝒱)] P_h`** — the DJ **`L(U)(0) ≅ U` as `A(𝒱)`-modules**.
* **`bottomActA_ker_restrictScalars`** — `(ker (bottomActA P)).restrictScalars ℂ = bottomBalancing`
  (by `rfl`): the `A(𝒱)`-quotient sits *definitionally* over the proved `ℂ`-object `MUBalBottom`, so the
  two agree as `ℂ`-spaces and `muBalBottomEquivA` refines `muBalBottomEquiv`.

This is the `n = 0` `A(𝒱)`-equivariant DJ statement — the module-level target the bimodule-balancing re-grading
must realize, and the `n = 0` case of "the mode action descends `A(𝒱)`-linearly" (B2).  No construction
file mutated; pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5 / Thm 4.13; Dong–Li–Mason III §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1 (Thm 5.3.4, easy direction `moduleMh`).
-/

namespace VOA

open scoped BigOperators DirectSum TensorProduct
open VertexOperatorAlgebra MUConstruct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

variable {W : VertexOperatorAlgebra 𝒱}

section AModule

variable (P : LWModule W)

-- The proved Zhu ring/algebra/module structures, as section-local instances.
noncomputable local instance instRingA_local : Ring (A W) := instRingA W
noncomputable local instance instAlgebraA_local : Algebra ℂ (A W) := instAlgebraA W
noncomputable local instance instModuleMh_local : Module (A W) P.toAMod.carrier := moduleMh W P.isLow

/-- **The `A(𝒱)`-linear R0 action map** `A(𝒱) ⊗_ℂ P_h → P_h`, `a ⊗ u ↦ ρ(a) u`.  Same underlying
function as `MUConstruct.bottomAct`; `A(𝒱)`-linearity is the module axiom `mul_smul`. -/
noncomputable def bottomActA : (A W ⊗[ℂ] P.toAMod.carrier) →ₗ[A W] P.toAMod.carrier where
  toFun := MUConstruct.bottomAct W P.toAMod
  map_add' := (MUConstruct.bottomAct W P.toAMod).map_add
  map_smul' := by
    intro b x
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
        rw [TensorProduct.smul_tmul', MUConstruct.bottomAct_tmul, MUConstruct.bottomAct_tmul]
        exact mul_smul b a u
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp] theorem bottomActA_tmul (a : A W) (u : P.toAMod.carrier) :
    bottomActA P (a ⊗ₜ[ℂ] u) = P.toAMod.ρ a u := rfl

/-- The `A(𝒱)`-linear R0 action map is surjective (`[𝟙] ⊗ u ↦ u`). -/
theorem bottomActA_surjective : Function.Surjective (bottomActA P) :=
  MUConstruct.bottomAct_surjective W P.toAMod

/-- **The balanced bottom as an `A(𝒱)`-module** `M(U)(0) = A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h`, realized as the
`ℂ`-tensor cover modulo the `A(𝒱)`-linear kernel `ker (bottomActA)`. -/
abbrev MUBalBottomA : Type u :=
  TensorProduct ℂ (A W) P.toAMod.carrier ⧸ LinearMap.ker (bottomActA P)

/-- **`M(U)(0) ≅ U` as `A(𝒱)`-modules** — the genuine Dong–Jiang level-`0` statement.  Descends
`bottomActA` through its kernel (`LinearMap.quotKerEquivOfSurjective`). -/
noncomputable def muBalBottomEquivA : MUBalBottomA P ≃ₗ[A W] P.toAMod.carrier :=
  LinearMap.quotKerEquivOfSurjective (bottomActA P) (bottomActA_surjective P)

@[simp] theorem muBalBottomEquivA_mk (a : A W) (u : P.toAMod.carrier) :
    muBalBottomEquivA P (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) = P.toAMod.ρ a u :=
  (LinearMap.quotKerEquivOfSurjective_apply_mk (bottomActA P) (bottomActA_surjective P)
    (a ⊗ₜ[ℂ] u)).trans (bottomActA_tmul P a u)

/-- **The `A(𝒱)`-quotient sits definitionally over the proved `ℂ`-object.**
`(ker (bottomActA P)).restrictScalars ℂ = bottomBalancing W P.toAMod` (by `rfl`, since `bottomActA` and
`bottomAct` share their underlying function).  So `MUBalBottomA P` and `MUBalBottom W P.toAMod` agree as
`ℂ`-spaces, and `muBalBottomEquivA` is the `A(𝒱)`-linear refinement of the proved `muBalBottomEquiv`. -/
theorem bottomActA_ker_restrictScalars :
    (LinearMap.ker (bottomActA P)).restrictScalars ℂ = MUConstruct.bottomBalancing W P.toAMod := rfl

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).

end AModule

end VOA
