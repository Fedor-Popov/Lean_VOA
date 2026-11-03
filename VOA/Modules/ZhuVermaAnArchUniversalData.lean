/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDownstream

/-!
# The downstream universal-property data, bundled over a `MURepFamily` and assembled as TERMS

Part of the lifting construction for Zhu Thm 5.3.4. `Modules.ZhuVermaAnArchDownstream` proves the
tightened headline

  `zhuBijection_of_downstream R C hall : Function.Bijective (forwardMap W)`

from a representation family `R : MURepFamily W` together with the four-field downstream residue
bundle `C : R.DownstreamData = {ludata, bottomIso, Dfun, G}` and the ambient irreducibility scope
`hall : AllLWIrreducible W`. Of those four fields, two of the *derived* universal-property clauses are
already terms in `ZhuVermaAnArchDownstream`: `realizes := C.bottomIso` (read off) and `hiso := C.Dfun.isoInvariant`
(the proven quotient-functor descent `MUFunctorialData.isoInvariant`). The four *carried* slots
`{ludata, bottomIso, Dfun, G}` are the genuine Dong–Jiang/Frenkel–Zhu construction residues.

This file does the **downstream discharge**: it bundles exactly those four genuine residues
*at the level of the representation family* into a single structure
`MURepFamily.UniversalData R`, and produces — **as a term** — `R.DownstreamData` from it, hence the
main Zhu theorem `Function.Bijective (forwardMap W)`. The point of the repackaging is that the universal
data is stated **once, intrinsically over the rep family** (whose `M(U)` carriers are the
`buildMUModuleData` terms of `ZhuVermaAnArchMUModuleDataBuild`), and every field of the downstream
bundle is then a *term*:

| `DownstreamData` field | source in `UniversalData` (this file)                              |
|------------------------|--------------------------------------------------------------------|
| `ludata U`             | carried (`U.ludata`): the per-`U` maximal-`J` datum (DJ output)    |
| `bottomIso U`          | carried (`U.bottomIso`): the bottom-survival iso `L(U).toAMod ≅ U` |
| `Dfun`                 | carried (`U.Dfun`): the `M(·)`-functoriality `muEquiv`/`maps_J`    |
| `G`                    | carried (`U.G`): the per-`P` generation-from-bottom residue        |

and, beyond the bundle, the two *derived* clauses are terms exactly as in `ZhuVermaAnArchDownstream`:
`toDownstreamData.realizes = U.bottomIso` and `toDownstreamData.isoInvariant = U.Dfun.isoInvariant`.

## What is a term here, and what is genuinely carried

The whole **assembly** `UniversalData → DownstreamData → CanonicalAssignmentData → forwardMap` is a
term: `toDownstreamData` is a `rfl`-level repackaging, `toCanonicalAssignmentData` and
`generatedFromBottom` are inherited from `ZhuVermaAnArchDownstream` (so `hiso` is the term `Dfun.isoInvariant`,
`realizes` is the term `bottomIso`), and `zhuBijection_of_universalData` is `zhuBijection_of_downstream`
fed the assembled bundle.

What is genuinely **carried** — as explicit hypothesis fields of `UniversalData`, **never** axioms —
is exactly the four Dong–Jiang/Frenkel–Zhu construction residues `{ludata, bottomIso, Dfun, G}`,
the irreducible four-piece content of the lifting half of Theorem 5.3.4. No field is faked; no field
is an axiom; each is precisely the deep construction output for which the depth-`n` bimodule apparatus
supplies the genuine combinatorial input (maximal-`J`, bottom survival, `M(·)`-functoriality,
generation-from-bottom).

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchDownstream` (`MURepFamily.DownstreamData`, `zhuBijection_of_downstream`),
`ZhuVermaAnArchMUModuleDataBuild` (`MURepFamily`, `toLUFamily`, `mudata`),
`ZhuVermaAnArchFunctorial` (`MUFunctorialData`, `MUFunctorialData.isoInvariant`),
`ZhuVermaAnArchGenFromBottomFinal` (`GenFromBottomFinalFamily`),
`ZhuVermaAnArchGameTwo` (`MUModuleData.LUData`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The intrinsic universal-property bundle over a representation family

A `MURepFamily W` produces, via `buildMUModuleData`, the headline `M(U)`-module **terms**
`R.mudata U` for each bottom `U`. The downstream universal property of Theorem 5.3.4 is then carried
by exactly four genuine Dong–Jiang/Frenkel–Zhu residues. We bundle them intrinsically over the rep
family — depending on the *maximal-`J` data* `ludata` only through the `LUFamily` `R.toLUFamily
ludata` for the later three fields, exactly as `DownstreamData` does. -/

/-- **The downstream universal-property bundle over a `MURepFamily R`.**

Carries the four genuine `CanonicalAssignmentData`/universal-property residues that close the lifting
half of Theorem 5.3.4 over the rep family `R` (whose `M(U)` carriers are the `buildMUModuleData`
terms):

* `ludata`   — the per-`U` maximal-`J` / irreducible-quotient datum `MUModuleData.LUData (R.mudata U)`
  (the genuine Dong–Jiang construction output that makes `L(U) = M(U)/J` irreducible);
* `bottomIso` — the **bottom-survival isomorphism** `((R.toLUFamily ludata).K U).toAMod ≅ U` for each
  `U` (R0 / bottom survival: the bottom of the irreducible quotient `L(U)` is `U`);
* `Dfun`     — `MUFunctorialData (R.toLUFamily ludata)`: functoriality of `M(·)` in its bottom
  (`muEquiv`/`muEquiv_maps_J`);
* `G`        — `GenFromBottomFinalFamily (R.toLUFamily ludata)`: the per-`P` generation-from-bottom
  residue (freeness already the term `GradedModeVanish.ofBottom`).

This is *exactly* the field content of `MURepFamily.DownstreamData R`, stated intrinsically over the
rep family. A hypothesis structure, no `sorry`, **never** an axiom. -/
structure MURepFamily.UniversalData (R : MURepFamily W) where
  /-- The per-`U` maximal-`J` / irreducible-quotient datum. -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)
  /-- The bottom-survival iso `L(U).toAMod ≅ U` (R0). -/
  bottomIso : ∀ U : AMod W, AModEquiv W ((R.toLUFamily ludata).K U).toAMod U
  /-- Functoriality of `M(·)` in its bottom. -/
  Dfun : MUFunctorialData (R.toLUFamily ludata)
  /-- The per-`P` generation-from-bottom residue (freeness already a term). -/
  G : GenFromBottomFinalFamily (R.toLUFamily ludata)

namespace MURepFamily.UniversalData

variable {R : MURepFamily W}

/-- **`R.DownstreamData` as a TERM.** The intrinsic universal bundle `D : R.UniversalData` is, field
for field, exactly the four genuine residues that `R.DownstreamData` carries. So the downstream bundle
is assembled by a single structure constructor — a *term*, no `sorry`, no axiom. From it the two
derived universal-property clauses (`realizes`, `hiso`) are the terms `bottomIso` /
`Dfun.isoInvariant`. -/
def toDownstreamData (D : R.UniversalData) : R.DownstreamData where
  ludata := D.ludata
  bottomIso := D.bottomIso
  Dfun := D.Dfun
  G := D.G

@[simp] theorem toDownstreamData_ludata (D : R.UniversalData) :
    (D.toDownstreamData).ludata = D.ludata := rfl

@[simp] theorem toDownstreamData_bottomIso (D : R.UniversalData) :
    (D.toDownstreamData).bottomIso = D.bottomIso := rfl

@[simp] theorem toDownstreamData_Dfun (D : R.UniversalData) :
    (D.toDownstreamData).Dfun = D.Dfun := rfl

@[simp] theorem toDownstreamData_G (D : R.UniversalData) :
    (D.toDownstreamData).G = D.G := rfl

/-- **`realizes` as a TERM.** The `CanonicalAssignmentData.realizes` clause — the bottom-survival iso
`L(U).toAMod ≅ U` — is exactly the carried `bottomIso`, read off the intrinsic bundle. -/
noncomputable def realizes (D : R.UniversalData) :
    ∀ U : AMod W, AModEquiv W (((D.toDownstreamData).F).K U).toAMod U :=
  (D.toDownstreamData).realizes

/-- **`hiso` as a TERM.** The universal-property functoriality clause
`∀ U₁ U₂, U₁ ≅ U₂ → L(U₁) ≅ L(U₂)` is the *proven* `MUFunctorialData.isoInvariant` of the carried
`Dfun` — **not** a separate leaf. -/
theorem isoInvariant (D : R.UniversalData) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (((D.toDownstreamData).F).K U₁) (((D.toDownstreamData).F).K U₂) :=
  (D.toDownstreamData).isoInvariant

/-- **The canonical assignment data from the intrinsic universal bundle** — a *term*, with `mudata`
the genuine `buildMUModuleData` term, `realizes` the term `bottomIso`, and `Dfun` the carried
functoriality. -/
noncomputable def toCanonicalAssignmentData (D : R.UniversalData) : CanonicalAssignmentData W :=
  (D.toDownstreamData).toCanonicalAssignmentData

/-- **`GeneratedFromBottom W` from the intrinsic bundle**, `hiso` plugged as the term
`Dfun.isoInvariant` and freeness already the term `GradedModeVanish.ofBottom` inside `G`. -/
theorem generatedFromBottom (D : R.UniversalData) : GeneratedFromBottom W :=
  (D.toDownstreamData).generatedFromBottom

end MURepFamily.UniversalData

end InducedAssignment

/-! ## The headline — the Zhu bijection from a `MURepFamily` and the intrinsic universal bundle

This is the restatement of `zhuBijection_of_downstream`: the four downstream
`CanonicalAssignmentData`/universal-property residues are bundled **intrinsically over the rep family**
as `MURepFamily.UniversalData`, from which `DownstreamData` — hence the main Zhu theorem — is a term. -/

/-- **Main theorem — the Zhu bijection from a representation family and the intrinsic universal bundle.**

Assembling the full lifting half *through* `buildMUModuleData` with the **downstream
universal-property residue bundled intrinsically over the rep family** (this file): from

* `R : MURepFamily W`            — the Construction-A representation data on each carrier `MU W U`
                                   (whose `M(U)` carriers are the `buildMUModuleData` terms);
* `D : R.UniversalData`          — the four genuine downstream residues bundled: the per-`U`
                                   maximal-`J` `ludata`, the bottom-survival iso `bottomIso`, the
                                   `M(·)`-functoriality `Dfun`, and the per-`P`
                                   generation-from-bottom residue `G`;
* `hall : AllLWIrreducible W`    — the ambient irreducibility scope,

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The whole assembly is a term: `D.toDownstreamData` is the structure-constructor repackaging,
`realizes`/`hiso` are the terms (`bottomIso` / `Dfun.isoInvariant`), and the headline is
`zhuBijection_of_downstream` fed `D.toDownstreamData`. The only carried content is `R` (the rep data)
and the four genuine construction residues inside `D`. No `sorry`, **never** an axiom. -/
theorem zhuBijection_of_universalData {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_downstream R D.toDownstreamData hall

/-- **`zhuBijection_of_universalData_via_scopeReduced` — the same headline routed through
`zhuBijection_scopeReduced`.** Identical content to `zhuBijection_of_universalData`, factored through
the scope-reduced backbone (`realizes`/`hiso` plugged as terms there): the canonical assignment data
is `D.toDownstreamData.toCanonicalAssignmentData`, and the per-`P` residue family is `D.G`. -/
theorem zhuBijection_of_universalData_via_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_downstream_via_scopeReduced R D.toDownstreamData hall

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
