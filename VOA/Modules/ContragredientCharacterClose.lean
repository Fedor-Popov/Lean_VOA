/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientCharacter
import VOA.Modules.ContragredientClose

/-!
# The contragredient one-point function, unconditional (quasi-primary)

`Modules/ContragredientCharacter` proves the one-point refinement
`χ_{M*}(τ,v) = (-1)ⁿ χ_M(τ,v)` for quasi-primary `v ∈ 𝒱ₙ` (`L₁v=0`), **parametric in the module
Jacobi hypothesis `ContragredientJacobi N`**.  That hypothesis is a proved theorem
(`contragredientJacobi_holds N`, `Modules/ContragredientClose`, discharged from the residual
`dualAdjResidualMvec_holds`), so this file exposes the refinement with **no `ContragredientJacobi`
hypothesis** — the contragredient one-point character for quasi-primary states is unconditional.

(The `contragredientJacobi_holds`-fed module is definitionally `contragredientFromResidual N`.)
`sorry`-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, `pbw`-free.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M] {v : 𝒱}

/-- **The contragredient coefficientwise trace identity, unconditional** (quasi-primary `v`): the
graded trace of the contragredient zero-mode block is `(-1)ⁿ` times `N`'s — with the module Jacobi
`ContragredientJacobi N` discharged by `contragredientJacobi_holds`. -/
theorem trace_weightBlock_contra_holds (N : OrdVModule W M) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) (α : ℂ) [FiniteDimensional ℂ (N.weight α)] :
    LinearMap.trace ℂ (RestrictedDual.weight N α)
        (weightBlock (contragredientFromResidual N)
          (oMod (contragredientFromResidual N) v) α)
      = (-1 : ℂ) ^ n • LinearMap.trace ℂ _ (weightBlock N (oMod N v) α) :=
  trace_weightBlock_contra N (contragredientJacobi_holds N) hvn hv α

/-- **The contragredient one-point function, unconditional** (Gannon §5.3.13, for quasi-primary
`v`).  For homogeneous quasi-primary `v ∈ 𝒱ₙ` (`W.L 1 v = 0`),
`χ_{M*}(τ, v) = (-1)ⁿ χ_M(τ, v)` — **with no `ContragredientJacobi` hypothesis** (discharged by
`contragredientJacobi_holds`).  This closes the contragredient one-point character for
quasi-primary states. -/
theorem onePoint_contragredient_holds (N : OrdVModule W M) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) :
    onePoint (contragredientFromResidual N) v = (-1 : ℂ) ^ n.toNat • onePoint N v :=
  onePoint_contragredient N (contragredientJacobi_holds N) hvn hv

end VOA
