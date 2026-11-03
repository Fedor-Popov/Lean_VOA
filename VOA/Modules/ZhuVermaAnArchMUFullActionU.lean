/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullAction
import VOA.Modules.ZhuVermaAnArchLeftGradingResidualFull

/-!
# DJ's `M(U)` 𝒱-action, unconditional — the `LeftGradingResidual` residual is discharged.

`ZhuVermaAnArchMUFullAction` builds DJ's genuine `M(U)` mode operators `oFull` on the full-ideal pieces
`MUPieceFull W U m = A_{m,0}(𝒱) ⊗_ℂ U`, modulo the named residual `LeftGradingResidual W n 0 m` (the DJ
Lemma 2.8 left inclusion `V ∗ⁿ_{0,m} O'_{m,0} ⊆ O_{n,0}`).  `ZhuVermaAnArchLeftGradingResidualFull`
DISCHARGES that residual unconditionally (`leftGradingResidual_zero_gen`, DJ Lemma 2.5's right-factor
half).  This file feeds the discharged residual back in, giving the **unconditional** `M(U)` action:

* `oFullU W U n m v : MUPieceFull W U m →ₗ MUPieceFull W U n` — DJ's genuine level-`(m→n)` mode operator
  `o_{n,m}(v)`, `[g] ⊗ u ↦ [v *ⁿ_{0,m} g] ⊗ u`, with NO carried hypothesis;
* `oFullU_comp` — DJ Lemma 4.1 `o_{n,p}(a) ∘ o_{p,m}(b) = o_{n,m}(a *ⁿ_{m,p} b)`, unconditional (the
  multiplicative core of the module Jacobi, Gannon 5.3.1b / DJ Thm 4.13).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemma 4.1, Thm 4.13); `ZhuVermaAnArchMUFullAction` (`oFull`,
`oFull_comp_of_leftGrading`), `ZhuVermaAnArchLeftGradingResidualFull` (`leftGradingResidual_zero_gen`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped TensorProduct DirectSum

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **DJ's genuine `M(U)` 𝒱-mode operator `o_{n,m}(v)`, unconditional.**  The level-`(m→n)` component
`[g] ⊗ u ↦ [v *ⁿ_{0,m} g] ⊗ u` of the induced-module action, with the `LeftGradingResidual`
well-definedness residual discharged by `leftGradingResidual_zero_gen`. -/
noncomputable def oFullU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v : 𝒱) :
    MUPieceFull W U m →ₗ[ℂ] MUPieceFull W U n :=
  oFull W U n m v (leftGradingResidual_zero_gen W n m)

@[simp] theorem oFullU_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v g : 𝒱)
    (u : U.carrier) :
    oFullU W U n m v (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
      = mkAnmFull W n 0 (anmGen W n 0 m v g) ⊗ₜ[ℂ] u :=
  oFull_tmul W U n m v g (leftGradingResidual_zero_gen W n m) u

/-- The unconditional `M(U)` action is `ℂ`-linear in the acting vector `v` (on generators). -/
theorem oFullU_add_left (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) (v₁ v₂ g : 𝒱)
    (u : U.carrier) :
    oFullU W U n m (v₁ + v₂) (mkAnmFull W m 0 g ⊗ₜ[ℂ] u)
      = oFullU W U n m v₁ (mkAnmFull W m 0 g ⊗ₜ[ℂ] u) + oFullU W U n m v₂ (mkAnmFull W m 0 g ⊗ₜ[ℂ] u) :=
  oFull_add_left W U n m v₁ v₂ (leftGradingResidual_zero_gen W n m) g u

/-- **DJ Lemma 4.1, unconditional** — the composition property of the `M(U)` mode operators:
`o_{n,p}(a) ∘ o_{p,m}(b) = o_{n,m}(a *ⁿ_{m,p} b)` on `MUFull`, with all three `LeftGradingResidual`
hypotheses discharged by `leftGradingResidual_zero_gen`.  This is the multiplicative core of the module
Jacobi (Gannon 5.3.1b / DJ Thm 4.13), free of every carried residual. -/
theorem oFullU_comp (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m p : ℕ) (a b : 𝒱) :
    (oFullU W U n p a).comp (oFullU W U p m b) = oFullU W U n m (anmGen W n m p a b) :=
  oFull_comp_of_leftGrading W U n m p a b (leftGradingResidual_zero_gen W n p)
    (leftGradingResidual_zero_gen W p m) (leftGradingResidual_zero_gen W n m)

end VOA
