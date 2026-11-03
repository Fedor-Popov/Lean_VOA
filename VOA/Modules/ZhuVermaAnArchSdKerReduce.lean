/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSdGprimeKer
import VOA.Modules.ZhuVermaAnArchStructuralClose

/-!
# `KerStructData` reduced to the two `qCanon` fields — the four maximal-`J` fields proved as TERMS

`ZhuVermaAnArchSdGprimeKer` shrank the Track-B `StructuralData.G'` field to the per-irreducible-`P`
bundle `GprimeKerPerP F P`, whose non-gate content is the six-field maximal-`J` structural bundle
`KerStructData F P` (`ZhuVermaAnArchSdGprimeKer.lean:125`):

* `bottom`           — the realized bottom subspace of `M(P.toAMod)`;
* `bottom_ne_bot`    — the bottom is nonzero;
* `J_bottom_trivial` — `(F.ludata P.toAMod).J ⊓ bottom = ⊥`;
* `J_maximal`        — maximality of `(F.ludata P.toAMod).J` among bottom-trivial submodules;
* `q_ne_zero`        — the canonical lift `qCanon P ≠ 0`;
* `q_inj_on_bottom`  — `qCanon P` is injective on the bottom.

This file makes the observation that, for the **regen-built** family

  `F := G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)`

(the exact family that the Track-B leaf `G'` is instantiated at in `StructuralClose`), the maximal
`J` is *definitionally* the canonical maximal bottom-trivial graded submodule

  `(F.ludata P.toAMod).J = (F.mudata P.toAMod).supBotTrivialGraded`

(via `lumaxOfRegen`/`MaxJData.ofRegen` ▸ `toLUMaxData_J` ▸ `toLUData_J`, all `rfl`).  Choosing the
`bottom` to be the realized weight space `(F.mudata P.toAMod).toOrdVModule.weight (F.hU P.toAMod)`, the
**four** purely-structural fields become TERMS built from already-proven pieces (functions of `G`,
`bregen`):

* `bottom`           — `(F.mudata P.toAMod).toOrdVModule.weight (F.hU P.toAMod)` (a term, the realized
  weight space);
* `bottom_ne_bot`    — `MUModuleData.bottom_weight_ne_bot` (the realization lemma);
* `J_bottom_trivial` — `MUModuleData.supBotTrivialGraded_bottom_disjoint` (the `sup_bottom_disjoint`
  proved in `ZhuVermaAnArchLumaxSupDisjoint`);
* `J_maximal`        — `MUModuleData.supBotTrivialGraded_dom` applied to the `BotTrivialGraded`
  package of any bottom-trivial weak submodule, whose gradedness is `OrdVModule.submodule_isGraded`
  (the `L₀`-semisimplicity of `ZhuVermaAnArchL0Semisimple`).

The **two** remaining fields — `q_ne_zero` / `q_inj_on_bottom` — are genuinely about the assembled
lift `qCanon P` (its bottom component being an iso), i.e. the *bottom-survival* of the lift, tied to
the `q_act` gate / `MUGradedAction` content.  They are **not** derivable from the maximal-`J`
machinery, so they are carried, as the leaner two-field bundle `KerStructRegenData`.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`KerStructRegenData G bregen P`** — the two carried `qCanon`-lift fields (`q_ne_zero`,
  `q_inj_on_bottom`), for the regen-built family.
* **`KerStructRegenData.toKerStructData`** — the full `KerStructData F P` (all six fields) **as a
  term**, with the four maximal-`J` fields discharged and the two `qCanon` fields passed through.
* **`GprimeKerRegenPerP G bregen P`** — the leaner per-`P` bundle carrying only the gate bridge
  `q_act_of_graded` and the two-field `KerStructRegenData`.
* **`GprimeKerRegenPerP.toGprimeKerPerP`** — the SdGprimeKer `GprimeKerPerP F P` with `struct` the
  assembled term, `q_act_of_graded` passed through.
* **`GprimeKerRegenFamily G bregen`**, **`gprimeKerRegen_of_family`** — the per-`P` family and the
  resulting `GprimeKerFamily F` for the regen-built family, ready to feed `gprimeKer_of_family`.

## Honest residual

For the regen-built family the carried surface of the Track-B `G'` leaf is exactly:

* the single gate bridge `q_act_of_graded` (`MUGradedAction W → q_act` of `qCanon P`) — the Track-A
  keystone, NEVER re-proved here; **and**
* the two `qCanon`-lift fields `q_ne_zero` / `q_inj_on_bottom` (the bottom-survival of the assembled
  lift).

What became a TERM this cycle: the four maximal-`J` structural fields `bottom` / `bottom_ne_bot` /
`J_bottom_trivial` / `J_maximal` — reduced to `lumaxOfRegen`/`MaxJData.ofRegen`/
`supBotTrivialGraded_bottom_disjoint`/`supBotTrivialGraded_dom`/`bottom_weight_ne_bot`/
`submodule_isGraded`, all functions of `G` and `bregen`.  No `sorry`, no `axiom`, no `pbw`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; Gannon §5.3.1–§5.3.2,
Thm 5.3.4; `ZhuVermaAnArchSdGprimeKer` (`KerStructData`, `GprimeKerPerP`, `qCanon`),
`ZhuVermaAnArchStructuralClose` (`lumaxOfRegen`, `BottomRegenData`),
`ZhuVermaAnArchL0Semisimple` (`MaxJData.ofRegen`, `OrdVModule.submodule_isGraded`),
`ZhuVermaAnArchLumaxSupDisjoint` (`supBotTrivialGraded_bottom_disjoint`),
`ZhuVermaAnArchLumax` (`supBotTrivialGraded`, `supBotTrivialGraded_dom`, `BotTrivialGraded`),
`ZhuVermaAnArchMULW` (`bottom_weight_ne_bot`, `cweight_isInternal`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The regen-built family and its definitional maximal-`J` -/

/-- **The regen-built `LUFamily`** — `F := G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)`,
the exact family the Track-B leaf `G'` is instantiated at in `StructuralClose`. -/
noncomputable def regenFamily (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) : LUFamily W :=
  G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)

@[simp] theorem regenFamily_mudata (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (U : AMod W) :
    (regenFamily G bregen).mudata U
      = (G.toBimodGenuineConstructionA).toMURepFamily.mudata U := rfl

/-- **The maximal `J` of the regen-built family is `supBotTrivialGraded` — definitionally.**  Through
`lumaxOfRegen` → `MaxJData.ofRegen` → `toLUMaxData` (`toLUMaxData_J`) → `toLUData` (`toLUData_J`),
the `J` slot of the regen-built `ludata` at `U` is exactly the canonical maximal bottom-trivial graded
submodule of `M(U)`. -/
@[simp] theorem regenFamily_ludata_J (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (U : AMod W) :
    ((regenFamily G bregen).ludata U).J
      = ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U).supBotTrivialGraded := rfl

/-! ## The leaner two-field bundle -/

/-- **The two carried `qCanon`-lift fields** of `KerStructData` (`q_ne_zero`, `q_inj_on_bottom`), for
the regen-built family with the bottom fixed to the realized weight space.

The four maximal-`J` structural fields (`bottom`, `bottom_ne_bot`, `J_bottom_trivial`, `J_maximal`)
are NOT here: they are the terms assembled in `toKerStructData` from
`lumaxOfRegen`/`supBotTrivialGraded_bottom_disjoint`/`supBotTrivialGraded_dom`/`bottom_weight_ne_bot`/
`submodule_isGraded`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure KerStructRegenData (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (P : LWModule W) where
  /-- The canonical lift `qCanon P` is nonzero. -/
  q_ne_zero : qCanon P ≠ 0
  /-- The canonical lift is injective on the realized bottom weight space. -/
  q_inj_on_bottom :
    ∀ x ∈ ((regenFamily G bregen).mudata P.toAMod).toOrdVModule.weight
        ((regenFamily G bregen).hU P.toAMod),
      qCanon P x = 0 → x = 0

namespace KerStructRegenData

variable {G : BimodGenuineConstructionAUniform W} {bregen : BottomRegenData G} {P : LWModule W}

/-- **The full `KerStructData` (all six fields) as a TERM.**  The four maximal-`J` structural fields
are discharged from already-proven pieces (functions of `G`, `bregen`); the two `qCanon`-lift fields
are passed through from the leaner bundle.

* `bottom` := the realized weight space `(F.mudata P.toAMod).toOrdVModule.weight (F.hU P.toAMod)`;
* `bottom_ne_bot` := `MUModuleData.bottom_weight_ne_bot` (realization);
* `J_bottom_trivial` := `MUModuleData.supBotTrivialGraded_bottom_disjoint` (`sup_bottom_disjoint`),
  reindexed along `regenFamily_ludata_J` (`(F.ludata …).J = supBotTrivialGraded`, `rfl`);
* `J_maximal` := any weak `N` with `N ⊓ bottom = ⊥` is graded (`OrdVModule.submodule_isGraded`, using
  the internal grading `cweight_isInternal`), hence a `BotTrivialGraded`, hence `≤ supBotTrivialGraded`
  (`supBotTrivialGraded_dom`). -/
noncomputable def toKerStructData (H : KerStructRegenData G bregen P) :
    KerStructData (regenFamily G bregen) P := by
  classical
  -- Abbreviate the underlying `MUModuleData` `D := F.mudata P.toAMod`.
  set D := (G.toBimodGenuineConstructionA).toMURepFamily.mudata P.toAMod with hD
  -- The realized bottom weight space, at the lowest weight `h = F.hU P.toAMod`.
  set bot := D.toOrdVModule.weight ((regenFamily G bregen).hU P.toAMod) with hbot
  -- Chosen `Decomposition` instance for `submodule_isGraded` (from the internal ℂ-grading).
  letI : DirectSum.Decomposition D.toOrdVModule.weight :=
    DirectSum.IsInternal.chooseDecomposition D.toOrdVModule.weight D.cweight_isInternal
  exact
    { bottom := bot
      bottom_ne_bot := D.bottom_weight_ne_bot
      J_bottom_trivial := by
        -- `(F.ludata …).J = supBotTrivialGraded D` (rfl); the disjointness is proven.
        show ((regenFamily G bregen).ludata P.toAMod).J.carrier ⊓ bot = ⊥
        rw [regenFamily_ludata_J]
        exact D.supBotTrivialGraded_bottom_disjoint
      J_maximal := by
        intro N hN
        -- `N` is graded (`L₀`-semisimplicity), so it packages as a `BotTrivialGraded D`.
        show N.carrier ≤ ((regenFamily G bregen).ludata P.toAMod).J.carrier
        rw [regenFamily_ludata_J]
        have hNgr : OrdVModule.IsGradedSubmodule D.toOrdVModule N :=
          OrdVModule.submodule_isGraded D.toOrdVModule N
        exact D.supBotTrivialGraded_dom
          { Q := N, Q_graded := hNgr, Q_disjoint := hN }
      q_ne_zero := H.q_ne_zero
      q_inj_on_bottom := H.q_inj_on_bottom }

end KerStructRegenData

/-! ## The leaner per-`P` bundle and its upgrade to `GprimeKerPerP` -/

/-- **The leaner Track-B `G'` per-`P` bundle for the regen-built family**, carrying only the gate
bridge `q_act_of_graded` and the two-field `KerStructRegenData`.  Compared with `GprimeKerPerP`
(`ZhuVermaAnArchSdGprimeKer.lean:152`) this **drops** the four maximal-`J` structural fields: they are
reconstructed as terms in `toGprimeKerPerP`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure GprimeKerRegenPerP (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (P : LWModule W) where
  /-- **The gate bridge — `q_act = MUGradedAction`** for the canonical lift `qCanon P` (verbatim the
  `GprimeKerPerP.q_act_of_graded` field at `F := regenFamily G bregen`). -/
  q_act_of_graded : MUGradedAction W →
    ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
      (DirectSum.toModule ℂ ℕ P.carrier
          (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n))
          (((regenFamily G bregen).mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
        = P.isMod.toWeakModule.act u n
            ((DirectSum.toModule ℂ ℕ P.carrier
              (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n)) x)
  /-- The two carried `qCanon`-lift fields (the four maximal-`J` fields are terms). -/
  regenStruct : KerStructRegenData G bregen P

namespace GprimeKerRegenPerP

variable {G : BimodGenuineConstructionAUniform W} {bregen : BottomRegenData G} {P : LWModule W}

/-- **The SdGprimeKer `GprimeKerPerP F P` (at `F := regenFamily G bregen`) as a term.**  The gate
bridge is passed through; `struct` is the assembled `KerStructData` from
`KerStructRegenData.toKerStructData` (four maximal-`J` fields are terms). -/
noncomputable def toGprimeKerPerP (H : GprimeKerRegenPerP G bregen P) :
    GprimeKerPerP (regenFamily G bregen) P where
  q_act_of_graded := H.q_act_of_graded
  struct := H.regenStruct.toKerStructData

end GprimeKerRegenPerP

/-! ## The per-`P` family and the SdGprimeKer `GprimeKerFamily` for the regen-built family -/

/-- **A per-irreducible-`P` family of the leaner two-field bundle** for the regen-built family.
(A `Prop`, since `GprimeKerRegenPerP` is all-`Prop` — its data-carrying analogue in `KerStructData`,
the `bottom` submodule, has been discharged to the term `weight (F.hU …)`.) -/
@[reducible] def GprimeKerRegenFamily (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) : Prop :=
  ∀ P : LWModule W, P.IsIrreducibleLW → GprimeKerRegenPerP G bregen P

/-- **The SdGprimeKer `GprimeKerFamily (regenFamily G bregen)` from the leaner family.**  For each
irreducible `P`, the leaner bundle `H P hP` upgrades (via `toGprimeKerPerP`) to the full
`GprimeKerPerP (regenFamily G bregen) P` with the four maximal-`J` structural fields as terms; only
the gate bridge and the two `qCanon`-lift fields remain carried.  Feed this into
`gprimeKer_of_family` (`ZhuVermaAnArchSdGprimeKer.lean:230`) to obtain the Track-B `G'` field.
No `sorry`, **never** an axiom. -/
noncomputable def gprimeKerRegen_of_family (G : BimodGenuineConstructionAUniform W)
    (bregen : BottomRegenData G) (H : GprimeKerRegenFamily G bregen) :
    GprimeKerFamily (regenFamily G bregen) :=
  fun P hP => (H P hP).toGprimeKerPerP

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
