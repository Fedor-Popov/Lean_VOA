/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUnivLift

/-!
# The per-layer bimodule action `layer n : A_{n,0}(𝒱) ⊗ U → P` (toward `UnivLiftData.layer`)

`Modules.ZhuVermaAnArchUnivLift` reduced the injective half of Zhu Theorem 5.3.4 to the bundled
per-layer data `UnivLiftData F P`, whose first field is

  `layer : ∀ n, MUPiece W P.toAMod n →ₗ[ℂ] P.carrier`

— a ℂ-linear map out of each graded layer `MUPiece W P.toAMod n = A_{n,0}(𝒱) ⊗_ℂ U`
(`ZhuVermaAnArchMU`), with `U = P.toAMod` the bottom (lowest-weight) `A(𝒱)`-module of `P`.  That file
carried the **whole** family `layer` as a hypothesis.

This file goes one structural level deeper and **constructs** each `layer n` out of:

* a **bottom map** `β : U → P` (the canonical identification of the bottom `U = P.toAMod` with the
  realized lowest-weight space `P_h ⊆ P`, followed by the inclusion); and
* the **per-layer graded mode action** of `𝒱` on the lowest-weight module `P`, namely the family of
  ℂ-linear maps `gradedAct n : 𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)` sending `a ↦ (the n-th graded mode of `a`
  acting on `β ·`, landing in the weight-`(h+n)` space of `P`)`.

The genuine **well-definedness** content — that the defining relations `O_{n,0}(𝒱)` of the bimodule
`A_{n,0}(𝒱) = 𝒱 / O_{n,0}(𝒱)` (`ZhuVermaAnArchAnm`) act as `0` through `gradedAct n` — is exactly the
graded analogue of the easy-direction `ZhuModule.actA` (the `O(𝒱)`-relations act as `0` on a genuine
`𝒱`-module's lowest-weight space).  We carry it as the precise hypothesis `gradedAct_descends`,
**never** an axiom; from it we descend `gradedAct n` through `A_{n,0}(𝒱)` (`Submodule.liftQ`) and
build `layer n := TensorProduct.lift (anmAct n)` — exactly the `TensorProduct.lift` ∘ `liftQ` pattern
of `ZhuVermaAnArchBimodComp.anmComposeBilin`.

## What is proved here (axiom-clean)

* `LayerActionData β P` — the per-layer graded-mode-action datum: the family
  `gradedAct n : 𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)` together with the `O_{n,0}`-descent
  `gradedAct_descends`.  A hypothesis structure, no `sorry`, **never** an axiom.
* `LayerActionData.anmAct n` — the descended ℂ-linear map `A_{n,0}(𝒱) →ₗ[ℂ] (U →ₗ[ℂ] P)`
  (`Submodule.liftQ` through `O_{n,0}` by `gradedAct_descends`), with the representative-evaluation
  lemma `anmAct_mk`.
* `LayerActionData.layerAction n` — **the per-layer ℂ-linear map** `MUPiece W P.toAMod n →ₗ[ℂ] P`,
  `[a] ⊗ u ↦ gradedAct n a u`, built as `TensorProduct.lift (anmAct n)`; representative-evaluation
  lemma `layerAction_tmul`.

The `O_{n,0}`-descent of the graded mode action is the structural well-definedness; it is the genuine
Dong–Jiang/Frenkel–Zhu freeness content of the bottom (DJ Prop 3.4–3.5, H. Li §2), carried here as
the data hypothesis `gradedAct_descends`, with `#print axioms` exactly
`[propext, Classical.choice, Quot.sound]`.

## The exact remaining statement

`layerAction` is the `UnivLiftData.layer` field constructed unconditionally from `LayerActionData`.
The genuine residual — for the full `UnivLiftData` (and hence the injective half) — is the supply of
a `LayerActionData β P` whose `gradedAct n` is the actual `n`-th graded mode action on `P`
*transported through* `β`, **plus** the assembled-map mode-intertwining `q_act` and kernel
`ker q = J`.  The single piece this file removes from the hypothesis surface is the *construction* of
each `layer n` (a `TensorProduct.lift` ∘ `liftQ`, not an input); the residual `gradedAct_descends`
is the precise `O_{n,0}`-descent of the graded mode action — the graded analogue of `actA`'s
`O_le_ker_rhoLW`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li `hep-th/9406211` §2; Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu;
`ZhuVermaAnArchMU` (`MUPiece`, `MU.incl`), `ZhuVermaAnArchAnm` (`Anm`, `Onm`, `mkAnm`),
`ZhuVermaAnArchBimodComp` (`anmComposeBilin` — the `TensorProduct.lift` ∘ `liftQ` pattern),
`ZhuModule` (`actA`, `O_le_ker_rhoLW` — the `n = 0` easy direction this graded-generalizes).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The per-layer graded-mode-action datum `LayerActionData` -/

/-- **The per-layer graded-mode-action datum on a lowest-weight module `P`, through a bottom map
`β : U → P`.**

For `U = P.toAMod` (the bottom `A(𝒱)`-module of `P`) and a bottom map `β : U → P` (the realized
embedding of the lowest-weight space `U ≅ P_h ↪ P`), this bundles the genuine Dong–Jiang/Frenkel–Zhu
freeness content of the bottom:

* `gradedAct n` — for each level `n`, the ℂ-linear map `𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)` sending a vertex-algebra
  vector `a ∈ 𝒱` to the **`n`-th graded mode action of `a` on `P` transported through `β`**:
  `a ↦ (u ↦ a₍·₎ (β u))`, landing in the weight-`(h+n)` space of `P`.  Linear in `a` and in `u`.
* `gradedAct_descends` — the **well-definedness**: the defining relations `O_{n,0}(𝒱)` of the
  bimodule `A_{n,0}(𝒱) = 𝒱 / O_{n,0}(𝒱)` act as `0` through `gradedAct n`.  This is the graded
  analogue of `ZhuModule.O_le_ker_rhoLW` (the `n = 0` easy direction), and is what makes the action
  descend to `A_{n,0}(𝒱)`.  Because `P` is a genuine `𝒱`-module, these relations act as `0` on the
  bottom; that is precisely the freeness content.

A hypothesis structure, no `sorry` and **never** an axiom. -/
structure LayerActionData {U : AMod W} {P : LWModule W}
    (β : U.carrier →ₗ[ℂ] P.carrier) where
  /-- The per-level graded mode action `𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)`, `a ↦ (u ↦ a₍·₎ (β u))`, the `n`-th
  graded mode of `a` acting on `β u`, landing in the weight-`(h+n)` space of `P`. -/
  gradedAct : ∀ n : ℕ, 𝒱 →ₗ[ℂ] (U.carrier →ₗ[ℂ] P.carrier)
  /-- **Well-definedness through `O_{n,0}(𝒱)`** (the graded analogue of `O_le_ker_rhoLW`): the
  bimodule relations `O_{n,0}(𝒱)` act as `0` through the graded mode action.  Because `P` is a
  genuine `𝒱`-module, these relations act as `0` on the bottom — the Dong–Jiang/Frenkel–Zhu freeness
  content of the bottom. -/
  gradedAct_descends : ∀ (n : ℕ), ∀ g ∈ Onm W n 0, gradedAct n g = 0

namespace LayerActionData

variable {U : AMod W} {P : LWModule W} {β : U.carrier →ₗ[ℂ] P.carrier}

/-! ## Descent of the graded mode action through `A_{n,0}(𝒱)` -/

/-- **The descended graded mode action** `A_{n,0}(𝒱) →ₗ[ℂ] (U →ₗ[ℂ] P)`.  The representative-level
graded mode action `gradedAct n : 𝒱 →ₗ[ℂ] (U →ₗ[ℂ] P)` descends through `A_{n,0}(𝒱) = 𝒱 / O_{n,0}(𝒱)`
(`Submodule.liftQ`), well-defined by `gradedAct_descends` (`O_{n,0} ≤ ker (gradedAct n)`).  This is
the graded generalization of `ZhuModule.actA` (the `n = 0` easy-direction action). -/
noncomputable def anmAct (L : LayerActionData β) (n : ℕ) :
    Anm W n 0 →ₗ[ℂ] (U.carrier →ₗ[ℂ] P.carrier) :=
  (Onm W n 0).liftQ (L.gradedAct n) (by
    intro g hg
    rw [LinearMap.mem_ker]
    exact L.gradedAct_descends n g hg)

/-- The descended action on a representative: `[a] ↦ gradedAct n a` (a map `U →ₗ P`). -/
@[simp] theorem anmAct_mk (L : LayerActionData β) (n : ℕ) (a : 𝒱) :
    L.anmAct n (mkAnm W n 0 a) = L.gradedAct n a := by
  rw [anmAct, mkAnm, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-! ## The per-layer ℂ-linear map `layer n : A_{n,0}(𝒱) ⊗ U → P` -/

/-- **The per-layer bimodule-action map** `MUPiece W U n = A_{n,0}(𝒱) ⊗_ℂ U →ₗ[ℂ] P`, sending
`[a] ⊗ u ↦ gradedAct n a u` — the `n`-th graded mode action of `a ∈ 𝒱` on `β u ∈ P_h`, landing in
the weight-`(h+n)` space of `P`.

Built as `TensorProduct.lift (anmAct n)` (the descended graded mode action `A_{n,0}(𝒱) →ₗ (U →ₗ P)`),
exactly the `TensorProduct.lift` ∘ `Submodule.liftQ` pattern of
`ZhuVermaAnArchBimodComp.anmComposeBilin`.  This is the constructed `UnivLiftData.layer n` field, with
the `O_{n,0}`-descent supplied by `gradedAct_descends`. -/
noncomputable def layerAction (L : LayerActionData β) (n : ℕ) :
    MUPiece W U n →ₗ[ℂ] P.carrier :=
  TensorProduct.lift (L.anmAct n)

/-- **Representative-evaluation lemma** for the per-layer map: `[a] ⊗ u ↦ gradedAct n a u`. -/
@[simp] theorem layerAction_tmul (L : LayerActionData β) (n : ℕ) (a : 𝒱) (u : U.carrier) :
    L.layerAction n (mkAnm W n 0 a ⊗ₜ[ℂ] u) = L.gradedAct n a u := by
  rw [layerAction, TensorProduct.lift.tmul, anmAct_mk]

/-- The per-layer map vanishes on a pure tensor whose left factor is a bimodule relation:
`[g] = 0` for `g ∈ O_{n,0}(𝒱)`, so `[g] ⊗ u ↦ 0` (the well-definedness, witnessed). -/
theorem layerAction_tmul_mem_Onm (L : LayerActionData β) (n : ℕ) {g : 𝒱}
    (hg : g ∈ Onm W n 0) (u : U.carrier) :
    L.layerAction n (mkAnm W n 0 g ⊗ₜ[ℂ] u) = 0 := by
  rw [layerAction_tmul, L.gradedAct_descends n g hg, LinearMap.zero_apply]

end LayerActionData

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
