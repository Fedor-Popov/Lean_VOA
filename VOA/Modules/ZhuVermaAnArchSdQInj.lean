/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdGprimeQ

/-!
# The `q_inj_on_bottom` leaf — reduced to level-`0` layer injectivity; NOT a term via R0 iso

The Track-B `G'` leaf's remaining non-gate field, packaged in
`ZhuVermaAnArchSdGprimeQ.qInjOnBottomResidual`, is injectivity of the canonical lift `qCanon P` on
the realized bottom weight space
`((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight ((regenFamily G bregen).hU P.toAMod)`.

One might hope to discharge this via the **proven R0 iso** `MUConstruct.bottomBalancedEquiv`
(`ZhuVermaAnArchMUConstruct.lean:124`), `(A(𝒱) ⊗_ℂ U) ⧸ ker(act) ≅ U`.  This file records the honest
outcome of that attempt:

## What genuinely reduces to a TERM

* **`weight_hU_eq_deg0`** — the realized bottom weight space *is* the level-`0` grading piece:
  `weight (hU) = MU.deg 0 = range (MU.incl 0)` (through `toOrdVModule_weight` + `cweight_cast 0`).
  This
  is the same identification `MUJNaturalCanonical`/`SdKerReduce` use, isolated here.

* **`qInjOnBottom_of_layerAction0_inj`** — the residual `qInjOnBottomResidual G bregen P` **follows
  from** injectivity of the level-`0` layer map
  `(ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction 0` on the
  pre-balancing piece `MUPiece W P.toAMod 0`.  Every bottom vector is `MU.incl 0 y` (bottom =
  `range (MU.incl 0)`); `MU.incl 0` is injective (`DirectSum.lof`, left inverse `MU.proj`); and
  `qCanon P (MU.incl 0 y) = layerAction 0 y` (the proved `qCanon_incl_zero`).  So the weight-space
  residual reduces to plain injectivity of `layerAction 0` — an axiom-clean TERM reduction.

## Why the R0 iso does NOT close the leaf (the honest residual)

`layerAction 0` on the pre-balancing piece is, by `qCanon_incl_zero` + `toLayerActionData` +
`gMode_zero`, exactly the composite `β ∘ act` where `act : A(𝒱) ⊗_ℂ P_h → P_h`, `a ⊗ w ↦ ρ a w` is
the R0 action map `MUConstruct.bottomAct` and `β = betaCanonical P` is the (injective) subtype
inclusion of the realized bottom.  Hence

  `ker (layerAction 0) = ker (bottomAct) = bottomBalancing`   (the R0 balancing submodule),

which is **nonzero** whenever `A(𝒱)` acts nontrivially on `P_h` (the balancing relations
`(a·r) ⊗ w − a ⊗ (r·w)`).  So `layerAction 0` is **not** injective on the pre-balancing cover, and
the hypothesis of `qInjOnBottom_of_layerAction0_inj` — hence `qInjOnBottomResidual` as literally
stated — is genuinely **false** on that carrier, NOT merely open.

`bottomBalancedEquiv` is an iso on the *quotient* `(A(𝒱) ⊗_ℂ U) ⧸ ker(act)`, i.e. it realizes `U`
only **after** dividing by exactly this balancing submodule.  `layerAction 0` factors as
`bottomBalancedEquiv ∘ (quotient projection)`, and the projection kills the (nonzero) balancing
submodule; the iso does **not** make the pre-balancing map injective.  So `bottomBalancedEquiv` does
not, and cannot, discharge the residual on the repo's pre-balancing `M(U)` carrier.

The genuine content of the leaf is therefore the R0 keystone itself: replacing the pre-balancing
level-`0` piece `A_{0,0}(𝒱) ⊗_ℂ P_h` by the balanced `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h`, which needs
`A(𝒱)` as a genuine `Ring` (the open Verma keystone).  On the *balanced* bottom the map is the iso
`bottomBalancedEquiv` and injectivity is immediate — but that is a statement about a different
carrier than the one `qCanon`/`MUPiece` currently use.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `weight_hU_eq_deg0` — realized bottom = `range (MU.incl 0)` (a TERM).
* `qInjOnBottom_of_layerAction0_inj` — the residual from level-`0` layer injectivity (a TERM
  reduction of the leaf to `Function.Injective (layerAction 0)` on the pre-balancing cover).

No `sorry`, no `axiom`, no new field is claimed as proved: `qInjOnBottomResidual` stays the honest
residual, reduced to the precise (and, on the pre-balancing carrier, false) injectivity of
`layerAction 0`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4, Thm 4.13; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchSdGprimeQ` (`qCanon_incl_zero`, `qInjOnBottomResidual`), `ZhuVermaAnArchMUConstruct`
(`bottomAct`, `bottomBalancing`, `bottomBalancedEquiv`, R0), `ZhuVermaAnArchMULW`
(`cweight_cast`, `toOrdVModule_weight`), `ZhuVermaAnArchMU` (`MU.incl`, `MU.deg`, `MU.proj`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The realized bottom weight space is the level-`0` grading piece -/

/-- **The realized bottom is `range (MU.incl 0)`.**  Through `toOrdVModule_weight` (the `OrdVModule`
weight is the ℂ-grading `cweight`) and `cweight_cast 0` (`cweight (h + 0) = MU.deg 0`), the realized
bottom weight space `weight (hU)` equals the level-`0` grading piece `MU.deg 0 = range (MU.incl 0)`.

`(regenFamily G bregen).mudata P.toAMod` is `MUModuleData W P.toAMod ((regenFamily …).hU P.toAMod)`,
so `hU` is exactly the `h`-parameter of the underlying `MUModuleData`, and `cweight ((h:ℂ)+0) =
cweight h` (since `(0 : ℕ)` casts to `0`). -/
theorem weight_hU_eq_deg0 (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (P : LWModule W) :
    ((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight
        ((regenFamily G bregen).hU P.toAMod)
      = MU.deg W P.toAMod 0 := by
  rw [MUModuleData.toOrdVModule_weight]
  have := ((regenFamily G bregen).mudata P.toAMod).cweight_cast 0
  simpa using this

/-! ## The residual reduces to level-`0` layer injectivity -/

/-- **`qInjOnBottomResidual` from level-`0` layer injectivity.**

If the level-`0` layer map
`(ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction 0` is injective on
the pre-balancing piece `MUPiece W P.toAMod 0`, then the realized-bottom injectivity residual
`qInjOnBottomResidual G bregen P` holds.

Every bottom vector `x ∈ weight (hU) = range (MU.incl 0)` (`weight_hU_eq_deg0`) is `MU.incl 0 y`;
`MU.incl 0 = DirectSum.lof …` is injective (left inverse `MU.proj 0`, `MU.proj_incl_same`); and
`qCanon P (MU.incl 0 y) = layerAction 0 y` (`qCanon_incl_zero`).  So `qCanon P x = 0` forces
`layerAction 0 y = 0`, hence `y = 0` by the hypothesis, hence `x = MU.incl 0 0 = 0`. -/
theorem qInjOnBottom_of_layerAction0_inj (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (P : LWModule W)
    (hinj : Function.Injective
      ((GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0)) :
    qInjOnBottomResidual G bregen P := by
  intro x hx hqx
  -- The realized bottom is `range (MU.incl 0)`.
  rw [weight_hU_eq_deg0, MU.deg, LinearMap.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  -- `qCanon P (MU.incl 0 y) = layerAction 0 y`, so the hypothesis gives `y = 0`.
  rw [qCanon_incl_zero] at hqx
  have hy : y = 0 := hinj (by rw [hqx, map_zero])
  rw [hy, map_zero]

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
