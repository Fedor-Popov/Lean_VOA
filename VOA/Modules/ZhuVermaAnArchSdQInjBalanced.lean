/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdQInj
import VOA.Modules.ZhuVermaAnArchBottomDefectClose

/-!
# `qInjOnBottomResidual` snapped to the proven R0 map — an honest frontier marker for the balanced-bottom keystone

**Status note (see `ZhuVermaAnArchSdBalancedBottom` for the audit-verified certificate).**  The
implication proved here, `bottomBalancing = ⊥ → qInjOnBottomResidual`, is axiom-clean and correct, but
its hypothesis `bottomBalancing W P.toAMod = ⊥` is **unsatisfiable** for every VOA with `dim A(𝒱) > 1`
(`bottomAct` is surjective, so its kernel is nonzero — proved as `qInjOnBottom_false_of_balancing_ne_bot`).
So this file *re-localizes* the balanced-bottom keystone to one crisp identity but does **not** discharge it; the genuine closure is
a construction-level change (realize the level-`0` carrier as the `A(𝒱)`-balanced tensor), the open
R0/generalized-Verma keystone.

`ZhuVermaAnArchSdQInj` reduced the injective-half leaf `qInjOnBottomResidual G bregen P`
(`ZhuVermaAnArchSdGprimeQ.lean:146`) to injectivity of the level-`0` layer map `layerAction 0`
on the pre-balancing bottom `MUPiece W P.toAMod 0 = A_{0,0}(𝒱) ⊗_ℂ P_h`, and *documented* (in
prose) that this map is `β ∘ bottomAct` with kernel the balancing submodule.  This file makes
that identification a **term** and pins the exact remaining identity.

## What is proved here (axiom-clean, no `sorry`)

* **`canonicalLayer0_bottomAct_tmul`** — the promised identification, as a theorem: on the bottom
  pure tensor `[a] ⊗ u`, the canonical level-`0` layer map is `β` of the R0 action map,
  `layerAction 0 ([a] ⊗ u) = β (bottomAct ([a] ⊗ u)) = o(a)(β u)`.  Proof: `toLayerActionData`
  `layerAction_tmul` + `gMode_zero` (`gMode 0 = oMod`) + `bottomAct_tmul` + the A(𝒱)-linearity
  of the realized bottom inclusion `actA_mk_apply_coe` (`(actA [a] u).coe = o(a)(u.coe)`, and
  `β = (P_h).subtype`).

* **`balancedBottom_injective`** — the **balanced-quotient injectivity term** the R0 iso delivers:
  `β ∘ bottomBalancedEquiv : (A_{0,0}(𝒱) ⊗_ℂ P_h) ⧸ bottomBalancing ≅ P_h ↪ P` is injective
  (`Subtype.coe_injective` ∘ `bottomBalancedEquiv.injective`).  This is injectivity on the
  **balanced** bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h` — precisely the statement that becomes
  `qInjOnBottom` once the pre-balancing carrier is replaced by the balanced tensor.

## The frontier marker (honest, but its hypothesis is unsatisfiable — NOT a route to a proof)

* **`qInjOnBottom_of_bottomBalancing_bot`** — `qInjOnBottomResidual G bregen P` is derived from
  the **single** hypothesis `bottomBalancing W P.toAMod = ⊥`.  Via
  `qInjOnBottom_of_layerAction0_inj` this reduces to `Function.Injective (layerAction 0)`, and
  `canonicalLayer0_bottomAct_tmul` (with `anmZeroEquivA [a]₀₀ = [a]`, both `rfl`) gives the
  **map factorization** `layerAction 0 = (β ∘ bottomAct) ∘ (anmZeroEquivA ⊗ id)`; the three
  factors are injective (`β` a `subtype`, `bottomAct` with kernel `bottomBalancing = ⊥`, and
  `anmZeroEquivA ⊗ id` a `LinearEquiv`).

This is a valid, axiom-clean implication.  **But it is not a discharge**: its hypothesis
`bottomBalancing W P.toAMod = ⊥` is a **false `Prop`** for every VOA with `dim A(𝒱) > 1`, because
`bottomAct : A(𝒱) ⊗_ℂ P_h ↠ P_h` is surjective and hence has kernel of ℂ-dimension
`(dim A(𝒱) − 1)·dim P_h > 0` (proved as `qInjOnBottom_false_of_balancing_ne_bot`, with the free-boson
witness `x ⊗ u₀ − 1 ⊗ (λ·u₀)`).  Correspondingly `qInjOnBottomResidual` — *"`qCanon` injective on the
full ℂ-tensor bottom"* — is itself false there.  The `ℂ`-tensor bottom `A_{0,0}(𝒱) ⊗_ℂ P_h` is
**strictly larger** than the balanced `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h ≅ P_h`; they are *not* equal.

So the true balanced-bottom keystone is **not** an identity provable on the current carrier — it is the *construction*
change that realizes `MUModuleData`'s level-`0` weight space as the balanced tensor (so that the
balancing is quotiented and `balancedBottom_injective` becomes the discharge).  That lives in the
`MU`/`MUModuleData` construction files (the open R0/generalized-Verma keystone), not here.
`balancedBottom_injective` above is exactly the injectivity that *already* holds on that balanced
quotient — the target the construction must reach.

`#print axioms` on all terms is `[propext, Classical.choice, Quot.sound]`.  No existing file
mutated; `MUGradedAction` is untouched.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5; H. Li hep-th/9406211 §2;
Gannon §5.3.1 (Thm 5.3.4 injective direction); `ZhuVermaAnArchMUConstruct` (`bottomAct`,
`bottomBalancing`, `bottomBalancedEquiv`), `ZhuModule` (`actA_mk_apply_coe`, `gMode_zero`),
`ZhuVermaAnArchSdQInj` (`qInjOnBottom_of_layerAction0_inj`).
-/

namespace VOA

open scoped BigOperators DirectSum TensorProduct
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The identification `layerAction 0 = β ∘ bottomAct` on the bottom, as a term -/

/-- **The canonical level-`0` layer map on the bottom pure tensor is `β` of the R0 action map.**
`layerAction 0 ([a] ⊗ u) = o(a)(β u) = β (bottomAct ([a] ⊗ u))`, where
`bottomAct : A(𝒱) ⊗_ℂ P_h → P_h` is the R0 action `[a] ⊗ u ↦ [a]·u` and `β = betaCanonical P` is
the (injective) realized-bottom inclusion `P_h ↪ P`.  This is the term-level form of the
`ZhuVermaAnArchSdQInj` prose identification — the reason `ker (layerAction 0) = bottomBalancing`. -/
theorem canonicalLayer0_bottomAct_tmul (P : LWModule W) (a : 𝒱) (u : (P.toAMod).carrier) :
    (GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0
        (mkAnm W 0 0 a ⊗ₜ[ℂ] u)
      = betaCanonical P (MUConstruct.bottomAct W P.toAMod (_root_.VOA.mk W a ⊗ₜ[ℂ] u)) := by
  rw [GradedModeVanish.toLayerActionData_layerAction_tmul, gMode_zero, MUConstruct.bottomAct_tmul]
  exact (actA_mk_apply_coe P.isMod P.isLow a u).symm

/-! ## The balanced-quotient injectivity term (the R0 iso's payoff) -/

/-- **The balanced bottom injects into `P`.**  `β ∘ bottomBalancedEquiv` is injective: the
composite `(A_{0,0}(𝒱) ⊗_ℂ P_h) ⧸ bottomBalancing  ≃  P_h  ↪  P` of the R0 balanced-bottom iso
`bottomBalancedEquiv` (`ZhuVermaAnArchMUConstruct.lean:124`) with the injective realized-bottom
inclusion `β = betaCanonical P`.  This is the injectivity `qInjOnBottom` genuinely asserts — but on
the **balanced** carrier `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h`, not the pre-balancing `ℂ`-tensor. -/
theorem balancedBottom_injective (P : LWModule W) :
    Function.Injective ((betaCanonical P) ∘ (MUConstruct.bottomBalancedEquiv W P.toAMod)) :=
  Subtype.coe_injective.comp (MUConstruct.bottomBalancedEquiv W P.toAMod).injective

/-! ## The residual, as a single Lean implication `bottomBalancing = ⊥ ⟹ qInjOnBottomResidual` -/

/-- **`A_{0,0}(𝒱) ≃ A(𝒱)`.**  The bottom-tower Zhu-block algebra is Zhu's algebra:
`Onm W 0 0 = O(𝒱)` (`Onm_zero_zero_eq_O`), so the quotients `𝒱 ⧸ Onm W 0 0` and `𝒱 ⧸ O(𝒱)`
coincide up to the canonical `Submodule.quotEquivOfEq`, which sends `[a]₀₀ ↦ [a]`
(representative-preserving, `rfl`). -/
noncomputable def anmZeroEquivA (W : VertexOperatorAlgebra 𝒱) : Anm W 0 0 ≃ₗ[ℂ] A W :=
  Submodule.quotEquivOfEq (Onm W 0 0) (O W) (Onm_zero_zero_eq_O W)

@[simp] theorem anmZeroEquivA_mkAnm (a : 𝒱) :
    anmZeroEquivA W (mkAnm W 0 0 a) = _root_.VOA.mk W a := rfl

/-- **The realized-bottom injectivity residual follows from `bottomBalancing = ⊥` (frontier marker).**

`qInjOnBottomResidual G bregen P` (a carried leaf of the injective half of Zhu Thm 5.3.4 at the bottom)
holds *if* the R0 balancing submodule of the pre-balancing `ℂ`-tensor bottom is trivial.

Proof.  By `qInjOnBottom_of_layerAction0_inj` it suffices that the level-`0` layer map is
injective.  That map **factors** as
`layerAction 0 = (β ∘ bottomAct) ∘ (anmZeroEquivA ⊗ id)` — the pointwise identity
`canonicalLayer0_bottomAct_tmul` (plus `anmZeroEquivA [a]₀₀ = [a]`, both by `rfl`) proves the map
equality on generators via `TensorProduct.ext'`.  The three factors are injective:
`anmZeroEquivA ⊗ id` is a `LinearEquiv`; `bottomAct` has kernel `bottomBalancing = ⊥` (hypothesis,
via `LinearMap.ker_eq_bot`); `β = betaCanonical P` is a `Submodule.subtype`
(`Subtype.coe_injective`).

**Caveat — this is a frontier marker, NOT a discharge of the balanced-bottom keystone.**  The hypothesis
`bottomBalancing W P.toAMod = ⊥` is a *false `Prop`* for every VOA with `dim A(𝒱) > 1`: `bottomAct` is
surjective, so `ker (bottomAct) = bottomBalancing` has ℂ-dimension `(dim A(𝒱) − 1)·dim P_h > 0`
(certified as `qInjOnBottom_false_of_balancing_ne_bot`, `ZhuVermaAnArchSdBalancedBottom`).  So this
implication has an unsatisfiable hypothesis there; it re-localizes the balanced-bottom keystone to one crisp identity but cannot
prove it.  The genuine closure is a *construction* change — realize `MUModuleData`'s level-`0` weight
space as the balanced tensor `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h ≅ P_h` (the open R0/generalized-Verma keystone,
in the `MU` construction files) — after which `balancedBottom_injective` is the discharge. -/
theorem qInjOnBottom_of_bottomBalancing_bot
    (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) (P : LWModule W)
    (hbal : MUConstruct.bottomBalancing W P.toAMod = ⊥) :
    qInjOnBottomResidual G bregen P := by
  refine qInjOnBottom_of_layerAction0_inj G bregen P ?_
  -- `layerAction 0 = (β ∘ bottomAct) ∘ (anmZeroEquivA ⊗ id)`.
  have hfac : (GradedModeVanish.ofBottom (betaCanonical P)
      (hbetaCanonical P)).toLayerActionData.layerAction 0
      = (betaCanonical P ∘ₗ MUConstruct.bottomAct W P.toAMod) ∘ₗ
          (TensorProduct.congr (anmZeroEquivA W)
            (LinearEquiv.refl ℂ (P.toAMod).carrier)).toLinearMap := by
    apply TensorProduct.ext'
    intro a u
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective (Onm W 0 0) a
    exact canonicalLayer0_bottomAct_tmul P a' u
  rw [hfac, LinearMap.coe_comp]
  refine Function.Injective.comp ?_
    (TensorProduct.congr (anmZeroEquivA W) (LinearEquiv.refl ℂ (P.toAMod).carrier)).injective
  rw [LinearMap.coe_comp]
  exact Subtype.coe_injective.comp (LinearMap.ker_eq_bot.mp hbal)

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
