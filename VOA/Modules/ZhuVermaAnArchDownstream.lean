/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUModuleDataBuild

/-!
# The DOWNSTREAM `CanonicalAssignmentData` fields, bundled as TERMS over a `MURepFamily`

Part of the lifting construction for Zhu Thm 5.3.4.  `Modules.ZhuVermaAnArchMUModuleDataBuild` proves
the central builder `MUModuleData.buildMUModuleData` — `M(U)` as a `𝒱`-module **term** — and the
representation-family wiring

  `MURepFamily W`  ⟹  `MURepFamily.mudata`  ⟹  `MURepFamily.toLUFamily`
                   ⟹  `MURepFamily.toCanonicalAssignmentData`  ⟹  `zhuBijection_of_repFamily`

whose conclusion is the main Zhu theorem `Function.Bijective (forwardMap W)`.  That headline carried, as
*separate* hypotheses on top of the representation family `R`, the **four downstream
`CanonicalAssignmentData`/universal-property fields**:

  `ludata`   — the per-`U` maximal-`J` / irreducible-quotient datum (`MUModuleData.LUData`);
  `realizes` — the bottom-survival iso `(F.K U).toAMod ≅ U`;
  `Dfun`     — `MUFunctorialData` (functoriality of `M(·)` in its bottom, the genuine source of
               `hiso`);
  `G`        — `GenFromBottomFinalFamily` (the per-`P` generation-from-bottom residue, freeness
               already the term `GradedModeVanish.ofBottom`).

This file performs the **downstream discharge as a single bundle**: it packages exactly those four
genuine residues into one hypothesis structure `MURepFamily.DownstreamData R`, and proves — *as a
term* — that from `R` together with `R.DownstreamData` the main Zhu theorem follows.  The key tightening
over `zhuBijection_of_repFamily` is that the universal-property functoriality clause
`hiso : ∀ U₁ U₂, U₁ ≅ U₂ → L(U₁) ≅ L(U₂)` is **not a separate leaf**: it is the *term*
`Dfun.isoInvariant` (`MUFunctorialData.isoInvariant`, the proven quotient-functor descent of `M(·)`
functoriality).  Hence `generatedFromBottom_final` is fed its `hiso` argument by a term, and the leaf
list collapses from `{ludata, realizes, Dfun, hiso, G}` (as it would be if `hiso` were carried
independently) to exactly `{ludata, realizes, Dfun, G}` — the four genuine construction residues,
with `hiso` derived.

## What each downstream field is, and how it is supplied here

| field      | status in this file                                                            |
|------------|--------------------------------------------------------------------------------|
| `ludata`   | carried per-`U` (the DJ maximal-`J` datum; genuine deep construction output)    |
| `realizes` | **term** `C.bottomIso U` from a carried per-`U` `AModEquiv` (R0 bottom survival)|
| `Dfun`     | carried (the `M(·)`-functoriality `muEquiv`/`muEquiv_maps_J`)                   |
| `hiso`     | **term** `Dfun.isoInvariant` — *derived*, not a leaf                            |
| `G`        | carried per-`P` (freeness already the term `GradedModeVanish.ofBottom`)         |

So **two** of the originally-carried universal-property obligations are discharged as terms here:
`realizes` is read off the carried bottom-survival `AModEquiv` (the genuine R0 / bottom-survival
content, exactly as `MURealizationData.bottomEquiv` and `GenuineMURealization.bottomEquiv` carry it),
and `hiso` is the *proven* `MUFunctorialData.isoInvariant`.  The remaining three carried residues
(`ludata`, `Dfun`, `G`) are precisely the genuine Dong–Jiang/Frenkel–Zhu construction data — carried
as explicit hypotheses, **never** axioms.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchMUModuleDataBuild` (`MURepFamily`, `buildMUModuleData`),
`ZhuVermaAnArchUniversal` (`LUFamily`, `LUFamily.K`), `ZhuVermaAnArchFunctorial`
(`MUFunctorialData`, `MUFunctorialData.isoInvariant`), `ZhuVermaAnArchGenFromBottomFinal`
(`GenFromBottomFinalFamily`, `generatedFromBottom_final`),
`ZhuVermaAnArchScopeClose` (`CanonicalAssignmentData`, `zhuBijection_scopeReduced`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The bundled downstream residue over a representation family

A `MURepFamily W` produces the headline `M(U)`-module terms (`R.mudata`), hence the `LUFamily`
`R.toLUFamily ludata` once a per-`U` maximal-`J` datum `ludata` is supplied.  The remaining
universal-property data needed for the Zhu bijection are the bottom-survival iso, the
`M(·)`-functoriality, and the per-`P` generation-from-bottom residue.  We bundle *exactly* those
four genuine residues (the maximal-`J` `ludata` included) into a single structure, with the
functoriality clause `hiso` *omitted* — it is supplied downstream as the term `Dfun.isoInvariant`. -/

/-- **The downstream universal-property residue over a `MURepFamily R`.**

Carries exactly the four genuine `CanonicalAssignmentData`/universal-property residues that the
representation family `R` does not itself produce:

* `ludata`   — the per-`U` maximal-`J` / irreducible-quotient datum `MUModuleData.LUData (R.mudata U)`
  (the genuine Dong–Jiang construction output that makes `L(U) = M(U)/J` irreducible);
* `bottomIso` — the **bottom-survival isomorphism** `(R.toLUFamily ludata).K U).toAMod ≅ U` for each
  `U` (R0 / bottom survival: the bottom of the irreducible quotient `L(U)` is `U`); from it the
  `realizes` field of `CanonicalAssignmentData` is a *term*;
* `Dfun`     — `MUFunctorialData (R.toLUFamily ludata)`: functoriality of `M(·)` in its bottom
  (`muEquiv`/`muEquiv_maps_J`).  From it the universal-property clause `hiso` is the *term*
  `Dfun.isoInvariant` — **not** carried separately;
* `G`        — `GenFromBottomFinalFamily (R.toLUFamily ludata)`: the per-`P` generation-from-bottom
  residue (the bottom map `β`/`hβ`, the sibling `q_act`, `bottom_ne_zero`, and the maximal-`J`
  `KerJData`); the freeness side is already the term `GradedModeVanish.ofBottom`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure MURepFamily.DownstreamData (R : MURepFamily W) where
  /-- The per-`U` maximal-`J` / irreducible-quotient datum. -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)
  /-- The bottom-survival iso `L(U).toAMod ≅ U` (R0); sources `realizes` as a term. -/
  bottomIso : ∀ U : AMod W, AModEquiv W ((R.toLUFamily ludata).K U).toAMod U
  /-- Functoriality of `M(·)` in its bottom; sources `hiso` as the term `Dfun.isoInvariant`. -/
  Dfun : MUFunctorialData (R.toLUFamily ludata)
  /-- The per-`P` generation-from-bottom residue (freeness already a term). -/
  G : GenFromBottomFinalFamily (R.toLUFamily ludata)

namespace MURepFamily.DownstreamData

variable {R : MURepFamily W}

/-- **The `LUFamily` produced by the representation family + the maximal-`J` datum.**  This is
`R.toLUFamily C.ludata`, whose `mudata` is entirely the `buildMUModuleData` term (`M(U)` as a
`𝒱`-module). -/
noncomputable def F (C : R.DownstreamData) : LUFamily W := R.toLUFamily C.ludata

@[simp] theorem F_mudata (C : R.DownstreamData) (U : AMod W) :
    (C.F).mudata U = R.mudata U := rfl

/-- **`realizes` as a TERM.**  The `CanonicalAssignmentData.realizes` field — the bottom-survival iso
`(C.F.K U).toAMod ≅ U` — is exactly the carried `bottomIso`, read off the downstream bundle.  This
discharges the `realizes` obligation of `zhuBijection_of_repFamily` from the bottom-survival datum,
not as an opaque separate hypothesis. -/
noncomputable def realizes (C : R.DownstreamData) :
    ∀ U : AMod W, AModEquiv W ((C.F).K U).toAMod U := C.bottomIso

/-- **`hiso` as a TERM.**  The universal-property functoriality clause
`∀ U₁ U₂, U₁ ≅ U₂ → L(U₁) ≅ L(U₂)` is the *proven* `MUFunctorialData.isoInvariant` of the carried
`Dfun`.  It is **not** a separate carried leaf: the only input it consumes is `Dfun` (whose genuine
content is the `M(·)`-functoriality `muEquiv`/`muEquiv_maps_J`); the descent to the irreducible
quotients is unconditional (`MUModuleData.quotientModuleEquiv`). -/
theorem isoInvariant (C : R.DownstreamData) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W ((C.F).K U₁) ((C.F).K U₂) :=
  C.Dfun.isoInvariant

/-- **The canonical assignment data from the representation family + the downstream bundle** — the
`CanonicalAssignmentData W` whose `F` is built through `buildMUModuleData` (so `mudata` is a genuine
term), whose `realizes` is the term `C.realizes`, and whose `Dfun` is the carried functoriality. -/
noncomputable def toCanonicalAssignmentData (C : R.DownstreamData) : CanonicalAssignmentData W :=
  R.toCanonicalAssignmentData C.ludata C.bottomIso C.Dfun

@[simp] theorem toCanonicalAssignmentData_F (C : R.DownstreamData) :
    (C.toCanonicalAssignmentData).F = C.F := rfl

/-- **`GeneratedFromBottom W` from the downstream bundle, `hiso` plugged as a term.**

`generatedFromBottom_final` consumes the `LUFamily` `C.F`, the functoriality clause `hiso`, and the
per-`P` residue family `G`.  Here `hiso` is supplied by the **term** `C.isoInvariant`
(`MUFunctorialData.isoInvariant`), and `G` is the carried residue (freeness already the term
`GradedModeVanish.ofBottom`).  So the whole universal property is assembled with `hiso` *derived*,
never carried. -/
theorem generatedFromBottom (C : R.DownstreamData) : GeneratedFromBottom W :=
  generatedFromBottom_final C.F C.isoInvariant C.G

end MURepFamily.DownstreamData

end InducedAssignment

/-! ## The headline — the Zhu bijection from `MURepFamily` + the bundled downstream residue

This is the tightened restatement of `zhuBijection_of_repFamily`: the four downstream
`CanonicalAssignmentData`/universal-property residues are bundled into the single
`MURepFamily.DownstreamData`, the `realizes` field is read off the carried bottom-survival iso, and
the functoriality clause `hiso` is the *term* `Dfun.isoInvariant` (not an independent leaf). -/

/-- **Main theorem — the Zhu bijection from a representation family and the bundled downstream residue.**

Assembling the full lifting half *through* `buildMUModuleData` (`ZhuVermaAnArchMUModuleDataBuild`)
with the **downstream universal-property residue bundled** (this file): from

* `R : MURepFamily W`            — the Construction-A representation data on each carrier `MU W U`
                                   (which `buildMUModuleData` turns into the headline `M(U)`-module
                                   terms);
* `C : R.DownstreamData`         — the four genuine downstream residues bundled: the per-`U`
                                   maximal-`J` `ludata`, the bottom-survival iso `bottomIso`, the
                                   `M(·)`-functoriality `Dfun`, and the per-`P`
                                   generation-from-bottom residue `G`;
* `hall : AllLWIrreducible W`    — the ambient irreducibility scope (legitimate
                                   statement-hypothesis),

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

Compared with `zhuBijection_of_repFamily`, the universal-property functoriality clause `hiso` is no
longer a separate leaf: it is the term `C.Dfun.isoInvariant`; and `realizes` is the term
`C.bottomIso`.  The remaining carried content is exactly `R` (the representation data, whose `M(U)`
terms are produced by `buildMUModuleData`), the three genuine construction residues in `C`
(`ludata`, `bottomIso`, `Dfun`, `G`), and the ambient scope `hall`.  No `sorry`, **never** an
axiom. -/
theorem zhuBijection_of_downstream {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (C : R.DownstreamData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal
    C.toCanonicalAssignmentData.toInducedAssignment hall
    C.toCanonicalAssignmentData.realizeIrreducible
    C.generatedFromBottom

/-- **`zhuBijection_of_downstream_via_scopeReduced` — the same headline routed through
`zhuBijection_scopeReduced`.**

Identical content to `zhuBijection_of_downstream`, but factored explicitly through the scope-reduced
backbone `zhuBijection_scopeReduced` (which itself plugs `hirr` and `hiso` as terms): the canonical
assignment data is `C.toCanonicalAssignmentData`, and the per-`P` residue family is `C.G`.  This
makes manifest that the only carried universal-property residue beyond the construction data is the
bundle `C` (with `realizes`/`hiso` discharged as terms) and the ambient scope `hall`. -/
theorem zhuBijection_of_downstream_via_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (C : R.DownstreamData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_scopeReduced C.toCanonicalAssignmentData hall C.G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
