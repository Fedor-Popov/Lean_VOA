/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdKerReduce
import VOA.Modules.ZhuVermaAnArchLeaf2

/-!
# G-prime's `qCanon`-fields — `q_ne_zero` proved as a TERM; `q_inj_on_bottom` the honest residual

`ZhuVermaAnArchSdKerReduce` reduced the Track-B `G'` leaf's non-gate content to the two-field bundle
`KerStructRegenData G bregen P` (`ZhuVermaAnArchSdKerReduce.lean:134`):

* `q_ne_zero`       — the canonical assembled lift `qCanon P ≠ 0`;
* `q_inj_on_bottom` — `qCanon P` is injective on the realized bottom weight space
  `((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight ((regenFamily G bregen).hU P.toAMod)`.

Here `qCanon P` (`ZhuVermaAnArchSdGprimeKer.lean:102`) is the direct-sum assembly
`⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n`, i.e.

  `qCanon P := DirectSum.toModule ℂ ℕ P.carrier (fun n => layerAction n)`.

## The reduction of the first `qCanon`-field — `q_ne_zero` (a TERM)

`qCanon P` composed with the bottom inclusion `MU.incl W P.toAMod 0 = DirectSum.lof ℂ ℕ _ 0` is,
by `DirectSum.toModule_lof`, exactly the level-`0` layer map `layerAction 0`:

  `qCanon P (MU.incl 0 y) = layerAction 0 y`      (`qCanon_incl_zero`).

The level-`0` layer map is the **already-proved** nonzero map `canonical_bottom_ne_zero`
(`ZhuVermaAnArchLeaf2.lean:79`, `layerAction 0 ≠ 0`, witnessed at the vacuum pure tensor `[𝟙] ⊗ u₀`
for a nonzero `u₀` in the realized bottom).  So there is a `y` with `layerAction 0 y ≠ 0`, hence
`qCanon P (MU.incl 0 y) ≠ 0`, hence `qCanon P ≠ 0`.  This is `qCanon_ne_zero` below — an
axiom-clean TERM, discharging the first `KerStructRegenData` field.

## The honest residual — `q_inj_on_bottom` does NOT reduce (R0 / balancing)

The second field, injectivity of `qCanon P` on the realized bottom, does **not** reduce to the
proved bottom-survival (`survOfRegen`) + `canonical_bottom_ne_zero`.  The reason is the
pre-balancing carrier of the repo's `M(U)`:

* The realized bottom is `weight (hU) = MU.deg 0 = range (MU.incl W P.toAMod 0)` (proved:
  `cweight_cast 0` ▸ `toOrdVModule_weight`, cf. `ZhuVermaAnArchMUJNaturalCanonical.lean:384`), and the
  level-`0` piece is the **pre-balancing** ℂ-tensor `MUPiece W P.toAMod 0 = A_{0,0}(𝒱) ⊗_ℂ P_h`
  (`ZhuVermaAnArchMU.lean:78`: *"the pre-balancing cover of the genuine `A_{n,0} ⊗_{A_0} U`"*).
* On that bottom, `qCanon P (MU.incl 0 y) = layerAction 0 y` and
  `layerAction 0 ([a] ⊗ u) = gMode P.isMod 0 a (β u) = a · (β u)` — the `A(𝒱)`-action on `β u`.
  Two distinct ℂ-tensors `(a · r) ⊗ u` and `a ⊗ (r · u)` are sent to the same vector `a · r · (β u)`
  but differ by a nonzero **balancing** element of `A(𝒱) ⊗_ℂ P_h`; so `layerAction 0` — and hence
  `qCanon P` on `range (MU.incl 0)` — has the whole balancing submodule in its kernel and is **not
  injective** on the pre-balancing bottom.  `layerAction 0` only becomes an iso onto `P_h` *after*
  quotienting by the balancing relation (the R0 iso `MUConstruct.bottomBalancedEquiv`,
  `A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h ≅ P_h`), which needs `A(𝒱)` to be a genuine `Ring` — the open Verma
  keystone flagged in `ZhuVermaAnArchMU.lean` (R0).

Bottom-survival (`survOfRegen`: `mkQ` injective on the bottom, kernel `J ⊓ M_h = ⊥`) is about a
*different* map — the quotient projection `mkQ : M(U) → L(U) = M(U)/J` — not the canonical lift
`qCanon P : M(U) → P`.  It gives injectivity of `mkQ` on the bottom, which does not transport to
injectivity of `qCanon P` on the same pre-balancing bottom (the two maps have different kernels: the
balancing submodule sits inside `ker (layerAction 0) ⊆ ker (qCanon P)` but is disjoint from `J`).

So `q_inj_on_bottom` is left as the **honest residual**: it is exactly the statement that
`layerAction 0` is injective on the pre-balancing bottom `A_{0,0}(𝒱) ⊗_ℂ P_h`, equivalently that the
R0 balanced-bottom quotient is trivial — the genuine R0 / balancing content, NOT the bottom-survival
of `mkQ`.  No `sorry`, no `axiom`: the field is simply not produced, and the residual is stated
precisely by `qInjOnBottomResidual` (a `def` recording the exact target `Prop`, so downstream code
can name it without any placeholder proof).

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`qCanon_incl_zero`** — `qCanon P (MU.incl W P.toAMod 0 y) = layerAction 0 y` (`toModule_lof`).
* **`qCanon_ne_zero`** — the first `KerStructRegenData` field `qCanon P ≠ 0`, as a TERM, from
  `canonical_bottom_ne_zero` through `qCanon_incl_zero`.
* **`qInjOnBottomResidual`** — the exact residual `Prop` for the second field (the R0
  balanced-bottom injectivity of `layerAction 0` on the pre-balancing bottom), a `def` (not proof).

## Honest residual

The Track-B `G'` leaf's non-gate content is exactly one field: `q_inj_on_bottom`, equal (through
`qCanon_incl_zero` and `weight (hU) = range (MU.incl 0)`) to the R0 balanced-bottom injectivity of
`layerAction 0`.  It is genuinely NOT reducible to `survOfRegen` (which is about `mkQ`, not
`qCanon`), and requires the R0 ring structure on `A(𝒱)`.  `q_ne_zero` is fully discharged.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4, Thm 4.13; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchSdGprimeKer` (`qCanon`), `ZhuVermaAnArchSdKerReduce` (`KerStructRegenData`,
`regenFamily`), `ZhuVermaAnArchLeaf2` (`canonical_bottom_ne_zero`, `canonicalLayer0_vacuum_tmul`),
`ZhuVermaAnArchMU` (`MU.incl`, `MUPiece`, pre-balancing carrier), `ZhuVermaAnArchMUConstruct`
(`bottomBalancedEquiv`, R0).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## `qCanon` on the bottom inclusion equals the level-`0` layer map -/

/-- **`qCanon P` on the bottom inclusion equals `layerAction 0`.**  `qCanon P` is
`DirectSum.toModule ℂ ℕ P.carrier (fun n => layerAction n)` and `MU.incl W P.toAMod 0` is
`DirectSum.lof ℂ ℕ _ 0`, so this is exactly `DirectSum.toModule_lof`. -/
theorem qCanon_incl_zero (P : LWModule W) (y : MUPiece W P.toAMod 0) :
    qCanon P (MU.incl W P.toAMod 0 y)
      = (GradedModeVanish.ofBottom (betaCanonical P)
          (hbetaCanonical P)).toLayerActionData.layerAction 0 y := by
  rw [qCanon, MU.incl, DirectSum.toModule_lof]

/-! ## First `qCanon`-field — `q_ne_zero` (a TERM) -/

/-- **`qCanon P ≠ 0`** — the first `KerStructRegenData` field, as a TERM.

If `qCanon P = 0` then `qCanon P ∘ MU.incl 0 = 0`, i.e. `layerAction 0 = 0` (by `qCanon_incl_zero`),
contradicting the proved `canonical_bottom_ne_zero` (`layerAction 0 ≠ 0`). -/
theorem qCanon_ne_zero (P : LWModule W) : qCanon P ≠ 0 := by
  intro hzero
  -- The level-`0` layer map is the zero map, contradicting `canonical_bottom_ne_zero`.
  refine canonical_bottom_ne_zero P ?_
  refine LinearMap.ext (fun y => ?_)
  rw [LinearMap.zero_apply, ← qCanon_incl_zero, hzero, LinearMap.zero_apply]

/-! ## Second `qCanon`-field — the honest R0 residual (NOT reduced) -/

/-- **The exact residual `Prop` for the second `KerStructRegenData` field** — injectivity of the
canonical lift on the realized bottom.  Through `qCanon_incl_zero` and
`weight (hU) = MU.deg 0 = range (MU.incl 0)`, this is precisely the R0 balanced-bottom injectivity
of `layerAction 0` on the **pre-balancing** bottom `MUPiece W P.toAMod 0 = A_{0,0}(𝒱) ⊗_ℂ P_h`.

It is genuinely NOT reducible to the proved bottom-survival `survOfRegen` (which concerns `mkQ`, not
`qCanon`; their kernels differ — the balancing submodule sits in `ker (qCanon)` but is disjoint from
the maximal `J`) nor to `canonical_bottom_ne_zero`.  It requires the R0 ring structure on `A(𝒱)`
(the open Verma keystone), which trivializes the balancing quotient
`A_{0,0}(𝒱) ⊗_{A(𝒱)} P_h ≅ P_h` (`MUConstruct.bottomBalancedEquiv`).

Recorded here as a `def` (the exact target `Prop`) — **not** a proof — so downstream code can name
the residual without any placeholder.  This is the verbatim `q_inj_on_bottom` field of
`KerStructRegenData G bregen P`. -/
def qInjOnBottomResidual (G : BimodGenuineConstructionAUniform W) (bregen : BottomRegenData G)
    (P : LWModule W) : Prop :=
  ∀ x ∈ ((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight
      ((regenFamily G bregen).hU P.toAMod),
    qCanon P x = 0 → x = 0

/-! ## `KerStructRegenData` from the single residual (`q_ne_zero` a term) -/

/-- **`KerStructRegenData G bregen P` from the single R0 residual.**  The first field `q_ne_zero` is
the proved TERM `qCanon_ne_zero`; only the second field — the R0 balanced-bottom injectivity,
packaged as `qInjOnBottomResidual G bregen P` — remains carried.  So the leaner two-field bundle is
reduced to a **one-field** hypothesis.  No `sorry`, no `axiom`. -/
noncomputable def kerStructRegen_of_residual (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (P : LWModule W)
    (hinj : qInjOnBottomResidual G bregen P) :
    KerStructRegenData G bregen P where
  q_ne_zero := qCanon_ne_zero P
  q_inj_on_bottom := hinj

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
