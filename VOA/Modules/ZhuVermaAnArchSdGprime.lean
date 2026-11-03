/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGenFromBottomG
import VOA.Modules.ZhuVermaAnArchStructuralClose
import VOA.Modules.ZhuVermaAnArchLeaf2

/-!
# `sd.G'` — the `GenFromBottomGFamily` field of `StructuralData` as a genuine term

This is the **Track-B `G'` field** of the structural bundle `StructuralData W`
(`ZhuVermaAnArchStructuralClose.lean:129`, field `G'`, line 139):

  `G' : GenFromBottomGFamily (G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData))`.

Feeding it (together with `A`, `hirr`, `G`, `bregen`) into `StructuralData` and thence
`bijection_of_structural` (`StructuralClose:151`) discharges the injective half of Zhu 5.3.4.

## What becomes a genuine term here, and what is carried

The per-irreducible-`P` residue `GenFromBottomGData F P` (`GenFromBottomG:123`) has seven fields.
Three of them are **retired to terms** here (they are genuinely independent of the deep DJ cores):

* `β`             := `betaCanonical P`            (`ZhuVermaAnArchTriageAudit`, TERM);
* `hβ`            := `hbetaCanonical P`           (`ZhuVermaAnArchTriageAudit`, TERM);
* `bottom_ne_zero`:= `canonical_bottom_ne_zero P` (`ZhuVermaAnArchLeaf2`, TERM).

The remaining fields are the **genuinely-open per-`P` leaves**, carried as a single precise
per-`P` hypothesis bundle `GprimePerP F P` (never a `sorry`, never an `axiom`):

* `q_act_of_graded` — **the gate bridge** `MUGradedAction W → <the assembled `ofBottom (betaCanonical
  P)`-lift intertwines every mode>`.  discharged once `MUGradedAction W` is supplied downstream
  (`GenFromBottomGData.toFinalData`); it is the DJ Prop 3.4 intertwining of the *specific* canonical
  lift, so it is stated against `betaCanonical P`/`hbetaCanonical P` on the nose;
* `kerData`        — the maximal-`J` first-isomorphism datum `KerJData (F.mudata P.toAMod) P` (from
  it `ker q = J` is the *derived* term `KerJData.ker_eq_J`, `ZhuVermaAnArchKerJ:246`);
* `hq`/`hJ`        — the two compatibility equations pinning `kerData.q` to the assembled canonical
  lift `⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P)).layer n` and `kerData.J` to
  `(F.ludata P.toAMod).J`.

So `G'` is assembled here as a genuine term of `GenFromBottomGFamily F` **modulo** the per-`P`
bundle `GprimePerP F` (`= ∀ P, P.IsIrreducibleLW → GprimePerP F P`): the freeness/β/hβ/bottom side
is entirely term-level (canonical bottom map + `GradedModeVanish.ofBottom` + `canonical_bottom_ne_zero`),
and the carried content is exactly the maximal-`J` `KerJData` + its two pins + the `MUGradedAction`
bridge — never re-proving `MUGradedAction` (the Track-A keystone), never `sorry`/`axiom`.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`GprimePerP F P`** — the per-`P` carried leaf bundle (q_act bridge + KerJData + two pins), with
  `β`/`hβ`/`bottom_ne_zero` NOT carried (they are the canonical terms).
* **`GprimePerP.toGData`** — assembles the full `GenFromBottomGData F P` (β/hβ/bottom_ne_zero plugged
  as terms, the four carried fields passed through).
* **`GprimeFamily F`** — the per-irreducible-`P` carried family.
* **`gprime_of_family`** — the target `GenFromBottomGFamily F` from `GprimeFamily F` (Track-B `G'`).
* **`sd_Gprime_of_family`** — `G'` specialized to the exact `StructuralData` family
  `F = G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)`, ready to drop into `StructuralData`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4, Thm 4.13; DLM3 §4; Gannon §5.3.2,
Thm 5.3.4; `ZhuVermaAnArchGenFromBottomG` (`GenFromBottomGData`, `GenFromBottomGFamily`),
`ZhuVermaAnArchTriageAudit` (`betaCanonical`, `hbetaCanonical`), `ZhuVermaAnArchLeaf2`
(`canonical_bottom_ne_zero`), `ZhuVermaAnArchKerJ` (`KerJData.ker_eq_J`),
`ZhuVermaAnArchStructuralClose` (`StructuralData`, `lumaxOfRegen`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The per-`P` carried leaf bundle (freeness/β/hβ/bottom are terms; only the hard fields carried) -/

/-- **The genuinely-open per-`P` leaves of the Track-B `G'` field, for the CANONICAL bottom map.**

For an irreducible lowest-weight `P` this bundles exactly the fields of `GenFromBottomGData F P`
that the depth-`n` bimodule apparatus has *not* yet collapsed to a term, **stated against the
canonical bottom map** `β = betaCanonical P` (so that `β`/`hβ`/`bottom_ne_zero` are supplied as the
terms `betaCanonical P` / `hbetaCanonical P` / `canonical_bottom_ne_zero P`):

* `q_act_of_graded` — the gate bridge `MUGradedAction W → <the assembled canonical lift intertwines
  every mode>` (the DJ Prop 3.4 intertwining of the specific `ofBottom (betaCanonical P)` lift;
  discharged downstream by the single Track-A keystone `MUGradedAction W`);
* `kerData`         — the maximal-`J` first-isomorphism datum `KerJData (F.mudata P.toAMod) P`;
* `hq`/`hJ`         — the two compatibility equations pinning `kerData.q` to the assembled canonical
  lift and `kerData.J` to `(F.ludata P.toAMod).J`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure GprimePerP (F : LUFamily W) (P : LWModule W) where
  /-- **The gate bridge — `q_act = MUGradedAction`** for the canonical lift.  Given the single
  Dong–Jiang keystone `MUGradedAction W`, the assembled canonical lift
  `q = ⨁ₙ (ofBottom (betaCanonical P) (hbetaCanonical P)).layer n` intertwines every mode. -/
  q_act_of_graded : MUGradedAction W →
    ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
      (DirectSum.toModule ℂ ℕ P.carrier
          (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n))
          ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
        = P.isMod.toWeakModule.act u n
            ((DirectSum.toModule ℂ ℕ P.carrier
              (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n)) x)
  /-- The maximal-`J` first-isomorphism datum (the only thing `ker q = J` rests on). -/
  kerData : KerJData (F.mudata P.toAMod) P
  /-- The `KerJData`'s intertwiner is the assembled canonical lift `q = ⨁ₙ layer n`. -/
  hq : kerData.q =
    DirectSum.toModule ℂ ℕ P.carrier
      (fun n => (GradedModeVanish.ofBottom (betaCanonical P) (hbetaCanonical P)).toLayerActionData.layerAction n)
  /-- The `KerJData`'s maximal submodule is `(F.ludata P.toAMod).J`. -/
  hJ : kerData.J = (F.ludata P.toAMod).J

namespace GprimePerP

variable {F : LUFamily W} {P : LWModule W}

/-- **The full per-`P` `GenFromBottomGData` from the carried bundle**, with `β`/`hβ`/`bottom_ne_zero`
plugged as the canonical terms `betaCanonical P` / `hbetaCanonical P` / `canonical_bottom_ne_zero P`
and the four genuinely-open fields (`q_act_of_graded`, `kerData`, `hq`, `hJ`) passed through.  No
`sorry`, **never** an axiom. -/
noncomputable def toGData (H : GprimePerP F P) : GenFromBottomGData F P where
  β := betaCanonical P
  hβ := hbetaCanonical P
  q_act_of_graded := H.q_act_of_graded
  bottom_ne_zero := canonical_bottom_ne_zero P
  kerData := H.kerData
  hq := H.hq
  hJ := H.hJ

end GprimePerP

/-! ## The per-`P` family and the Track-B `G'` term -/

/-- **A per-irreducible-`P` family of the carried leaf bundle.** -/
def GprimeFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → GprimePerP F P

/-- **The Track-B `G'` field — `GenFromBottomGFamily F` from the carried per-`P` family.**

For each irreducible `P`, the carried bundle `H P hP` upgrades to a full `GenFromBottomGData F P`
via `GprimePerP.toGData`: `β`/`hβ`/`bottom_ne_zero` are the canonical terms, and the four
genuinely-open fields (the `MUGradedAction`-bridged `q_act_of_graded`, the maximal-`J` `KerJData`,
and the two compatibility pins) are passed through.  This is exactly the `G'` field consumed by
`StructuralData` / `bijection_of_structural`. -/
noncomputable def gprime_of_family (F : LUFamily W) (H : GprimeFamily F) : GenFromBottomGFamily F :=
  fun P hP => (H P hP).toGData

end InducedAssignment

/-! ## `G'` specialized to the exact `StructuralData` family -/

/-- **`sd_Gprime_of_family` — the `StructuralData.G'` field for the exact bijection family.**

Specializes `gprime_of_family` to
`F = G.toLUFamily (fun U => (lumaxOfRegen G bregen U).toLUData)`, the precise `LUFamily` that
`StructuralData.G'` (`StructuralClose:139`) is indexed by.  The result is a genuine term of the
`GenFromBottomGFamily` type required by that field, modulo the carried per-`P` bundle family
`H` (freeness/β/hβ/bottom side all term-level; only the `MUGradedAction` bridge, the maximal-`J`
`KerJData`, and the two pins carried).  Drop it into `StructuralData` alongside `A`/`hirr`/`G`/
`bregen` to obtain `bijection_of_structural`. -/
noncomputable def sd_Gprime_of_family {W : VertexOperatorAlgebra 𝒱}
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (bregen : InducedAssignment.BottomRegenData G)
    (H : InducedAssignment.GprimeFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData))) :
    InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (InducedAssignment.lumaxOfRegen G bregen U).toLUData)) :=
  InducedAssignment.gprime_of_family _ H

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
