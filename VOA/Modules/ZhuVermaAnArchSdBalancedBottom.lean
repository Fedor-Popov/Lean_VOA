/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdQInjBalanced

/-!
# Diagnostics: the residual-as-stated is FALSE, and the correct bottom lives on the balanced quotient

`ZhuVermaAnArchSdQInjBalanced` produced the axiom-clean implication
`qInjOnBottom_of_bottomBalancing_bot : bottomBalancing W P.toAMod = ⊥ → qInjOnBottomResidual`.
Its hypothesis is **unsatisfiable** for every VOA with `dim A(𝒱) > 1` (checked against the code,
with the free-boson counterexample):

* `bottomAct : A(𝒱) ⊗_ℂ P_h → P_h` is ℂ-**surjective** (`bottomAct_surjective`), so by rank–nullity
  `ker (bottomAct) = bottomBalancing` has ℂ-dimension `(dim A(𝒱) − 1)·dim P_h > 0` whenever
  `dim A(𝒱) > 1`.  Concrete witness (free boson, `A(𝒱) = ℂ[x]`, `ρ(x) = λ`):
  `x ⊗ u₀ − 1 ⊗ (λ·u₀) ∈ bottomBalancing`, nonzero, killed by `bottomAct`.
* `qCanon P` restricted to the bottom `weight (hU) = range (MU.incl 0) = MUPiece 0 = A_{0,0}(𝒱) ⊗_ℂ P_h`
  equals `layerAction 0 = β ∘ bottomAct` (`qCanon_incl_zero` + `canonicalLayer0_bottomAct_tmul`), whose
  kernel is exactly the (nonzero) balancing.  Hence `qInjOnBottomResidual` — *"`qCanon` injective on the
  full ℂ-tensor bottom"* — is a **false `Prop`** for `dim A(𝒱) > 1`, not merely open.

So `qInjOnBottom_of_bottomBalancing_bot` is an **honest frontier marker**, not a route to a proof: a
valid implication with an unsatisfiable hypothesis.  The genuine closure of the balanced-bottom keystone is a *construction-level*
change — realize the level-`0` weight space of the induced module as the `A(𝒱)`-**balanced** tensor
`A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h ≅ P_h` (`bottomBalancedEquiv`) — which lives in the `MU`/`MUModuleData`
construction files, not the injective-half/reduction files, and is the open R0/generalized-Verma keystone.

## What this file adds (axiom-clean, injective-half-only, no construction change)

* **`bottomKer_eq_balancing`** — the exact always-true content: on the bottom, `ker (layerAction 0)`
  **is** the balancing, transported by `anmZeroEquivA ⊗ id`.  (So there is nothing to prove away: the
  kernel is precisely the balancing, nothing more, nothing less.)
* **`balancedBottomRealization`** — the correct Dong–Jiang statement `L(U)(0) ≅ U`, realized on the
  **balanced** quotient: `(A(𝒱) ⊗_ℂ P_h) ⧸ bottomBalancing ≃ₗ range (betaCanonical P)` (the copy of
  `P_h` inside `P`), from `bottomBalancedEquiv` and `LinearEquiv.ofInjective β`.
* **`qInjOnBottom_false_of_balancing_ne_bot`** — the certificate: `bottomBalancing ≠ ⊥` refutes
  `qInjOnBottomResidual`.  This is the *theorem form* of the audit's central finding; it proves the
  residual-as-stated is false whenever the balancing is nontrivial, so no one attempts to prove it.

`#print axioms` on all terms is `[propext, Classical.choice, Quot.sound]`.
The balanced-bottom keystone remains the open construction keystone.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5; H. Li hep-th/9406211 §2; Gannon §5.3.1;
`ZhuVermaAnArchMUConstruct` (`bottomAct`/`bottomBalancing`/`bottomBalancedEquiv`),
`ZhuVermaAnArchSdQInjBalanced` (`canonicalLayer0_bottomAct_tmul`/`balancedBottom_injective`/`anmZeroEquivA`),
`ZhuVermaAnArchSdGprimeQ` (`qCanon_incl_zero`/`qInjOnBottomResidual`), `ZhuVermaAnArchMU` (`MU.incl`/`deg`).
-/

namespace VOA

open scoped BigOperators DirectSum TensorProduct
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- `betaCanonical P` (the realized-bottom inclusion `P_h ↪ P`, a `Submodule.subtype`) is injective. -/
theorem betaCanonical_injective (P : LWModule W) :
    Function.Injective (betaCanonical P) := Subtype.coe_injective

/-- **The bottom layer map factors as `β ∘ bottomAct` through `anmZeroEquivA ⊗ id`.**  Extracted (as a
named theorem) from the factorization inside `qInjOnBottom_of_bottomBalancing_bot`: proved on generators
by `TensorProduct.ext'` + `canonicalLayer0_bottomAct_tmul` (all reductions `rfl`). -/
theorem layerAction0_factor (P : LWModule W) :
    (GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0
      = (betaCanonical P ∘ₗ MUConstruct.bottomAct W P.toAMod) ∘ₗ
          (TensorProduct.congr (anmZeroEquivA W)
            (LinearEquiv.refl ℂ (P.toAMod).carrier)).toLinearMap := by
  apply TensorProduct.ext'
  intro a u
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective (Onm W 0 0) a
  exact canonicalLayer0_bottomAct_tmul P a' u

/-! ## The always-true content: on the bottom, `ker (layerAction 0)` IS the balancing -/

/-- **`ker (layerAction 0)` on the bottom equals the balancing (transported by `anmZeroEquivA ⊗ id`).**
There is nothing to "prove away": the kernel of the bottom layer map is *exactly* the R0 balancing
submodule, pulled back along the `Anm₀₀ ≃ A(𝒱)` bridge.  `β` is injective and `anmZeroEquivA ⊗ id` is a
`LinearEquiv`, so the kernel is the comap of `bottomBalancing = ker (bottomAct)`. -/
theorem bottomKer_eq_balancing (P : LWModule W) :
    LinearMap.ker ((GradedModeVanish.ofBottom (betaCanonical P)
        (hbetaCanonical P)).toLayerActionData.layerAction 0)
      = Submodule.comap (TensorProduct.congr (anmZeroEquivA W)
          (LinearEquiv.refl ℂ (P.toAMod).carrier)).toLinearMap
          (MUConstruct.bottomBalancing W P.toAMod) := by
  rw [layerAction0_factor, LinearMap.ker_comp, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.mpr (betaCanonical_injective P), Submodule.comap_bot]
  rfl

/-! ## The correct DJ statement `L(U)(0) ≅ U`, on the balanced quotient -/

/-- **`L(U)(0) ≅ U`, realized on the balanced bottom.**  The balanced quotient
`(A(𝒱) ⊗_ℂ P_h) ⧸ bottomBalancing` is linearly isomorphic to `range (betaCanonical P)` — the copy of
`P_h = U` sitting inside `P`.  Composite of the R0 iso `bottomBalancedEquiv` (`≅ P_h`) with
`LinearEquiv.ofInjective β` (`P_h ≅ range β`).  This is the correct Dong–Jiang level-`0` statement; it is
the object the construction must realize as `MUModuleData`'s bottom in order to discharge the balanced-bottom keystone. -/
noncomputable def balancedBottomRealization (P : LWModule W) :
    (TensorProduct ℂ (A W) (P.toAMod).carrier ⧸ MUConstruct.bottomBalancing W P.toAMod)
      ≃ₗ[ℂ] (LinearMap.range (betaCanonical P)) :=
  (MUConstruct.bottomBalancedEquiv W P.toAMod).trans
    (LinearEquiv.ofInjective (betaCanonical P) (betaCanonical_injective P))

/-! ## The certificate: the residual-as-stated is FALSE when the balancing is nontrivial -/

/-- **`bottomBalancing ≠ ⊥` refutes `qInjOnBottomResidual`.**  The theorem form of the audit's central
finding.  A nonzero balancing vector `v`, transported to `w ∈ MUPiece 0` and included as
`x = MU.incl 0 w ∈ weight (hU)`, is a nonzero bottom vector with `qCanon P x = β (bottomAct v) = 0`
(`qCanon_incl_zero` + `layerAction0_factor`), so `qCanon` is *not* injective on the bottom.  Hence for
every VOA with `dim A(𝒱) > 1` (where `bottomBalancing ≠ ⊥` by surjectivity of `bottomAct`), the residual
`qInjOnBottomResidual G bregen P` is a **false `Prop`** — certifying `qInjOnBottom_of_bottomBalancing_bot`
as an honest-but-unusable frontier marker (valid implication, unsatisfiable hypothesis). -/
theorem qInjOnBottom_false_of_balancing_ne_bot
    (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G) (P : LWModule W)
    (hbal : MUConstruct.bottomBalancing W P.toAMod ≠ ⊥) :
    ¬ qInjOnBottomResidual G bregen P := by
  -- A nonzero balancing vector `v`, and its preimage `w ∈ MUPiece 0` under `anmZeroEquivA ⊗ id`.
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbal
  set e := TensorProduct.congr (anmZeroEquivA W) (LinearEquiv.refl ℂ (P.toAMod).carrier) with he
  have hw_ne : e.symm v ≠ 0 := fun h => hv_ne (by
    have := congrArg e h
    rwa [e.apply_symm_apply, map_zero] at this)
  have hv0 : MUConstruct.bottomAct W P.toAMod v = 0 := hv_mem
  intro hres
  -- The bottom vector `x = MU.incl 0 (e.symm v)`.
  have hx_mem : MU.incl W P.toAMod 0 (e.symm v)
      ∈ ((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight
          ((regenFamily G bregen).hU P.toAMod) := by
    rw [weight_hU_eq_deg0, MU.deg, LinearMap.mem_range]
    exact ⟨e.symm v, rfl⟩
  have hqx : qCanon P (MU.incl W P.toAMod 0 (e.symm v)) = 0 := by
    rw [qCanon_incl_zero, layerAction0_factor]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ← he]
    rw [e.apply_symm_apply, hv0, map_zero]
  -- `hres` forces `x = 0`, hence (`MU.incl 0` injective) `e.symm v = 0` — contradiction.
  have hx0 : MU.incl W P.toAMod 0 (e.symm v) = 0 := hres _ hx_mem hqx
  refine hw_ne ?_
  have hinj : Function.Injective (MU.incl W P.toAMod 0) :=
    Function.LeftInverse.injective (g := MU.proj W P.toAMod 0)
      (fun z => MU.proj_incl_same W P.toAMod 0 z)
  exact hinj (by rw [hx0, map_zero])

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
