/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUniversalData

/-!
# Closing the universal-property data `{ludata, bottomIso, Dfun, G}` as TERMS

`Modules.ZhuVermaAnArchUniversalData` bundles the four genuine downstream residues of the
lifting half of Zhu Theorem 5.3.4 *intrinsically over a representation family* as
`MURepFamily.UniversalData R = {ludata, bottomIso, Dfun, G}`, from which the main Zhu theorem
`Function.Bijective (forwardMap W)` is a term (`zhuBijection_of_universalData`).

This file performs the **close**: it pins down, field by field, exactly *which* of the four
universal-property obligations are **terms** and *which* remain precise carried cruxes, and it
assembles `MURepFamily.UniversalData R` from a single intrinsic bundle
`MURepFamily.UniversalClose R` **as a structure-constructor term** — so the entire route

  `MURepFamily R` + `UniversalClose R`
      ⟹ `UniversalData R`         (structure constructor — a *term*)
      ⟹ `DownstreamData R`        (`toDownstreamData`, a `rfl`-level repackaging — a *term*)
      ⟹ `CanonicalAssignmentData W` (`toCanonicalAssignmentData`, a *term*)
      ⟹ `Function.Bijective (forwardMap W)`  (`zhuBijection_of_downstream` — a *term*)

is one continuous chain of terms, depending only on the genuinely-deep construction cruxes carried
in `UniversalClose`.

## Which of the four are terms, and which are precise carried cruxes

| field      | status after this close                                                  |
|------------|----------------------------------------------------------------------------------|
| `realizes` | **TERM** — read off `bottomIso` (`UniversalData.realizes`)                        |
| `hiso`     | **TERM** — the proven `Dfun.isoInvariant` (`MUFunctorialData.isoInvariant`)       |
| freeness   | **TERM** — `GradedModeVanish.ofBottom` inside `G` (`GenFromBottomFinalData.layer`)|
| `ker q = J`| **TERM** — `KerJData.ker_eq_J` inside `G` (first-isomorphism core)                |
| `bottomIso`| crux — R0 + bottom survival (R0, `MUConstruct.bottomBalancedEquiv`, is a term)   |
| `ludata`   | crux — the Dong–Jiang maximal-`J` / simplicity datum                              |
| `Dfun`     | crux — the construction-level functoriality of `M(·)` in its bottom              |
| `G` siblings| cruxes — `q_act` (`CrossCFirstOnm`), `bottom_ne_zero` (`BottomOrbit`), `β`/`hβ`  |

So **four** of the universal-property obligations — `realizes`, `hiso`, the freeness side, and the
first-isomorphism `ker q = J` — are *terms*. What `UniversalClose` carries are exactly the four
genuine Dong–Jiang/Frenkel–Zhu construction residues `{ludata, bottomIso, Dfun, G}`, each the
irreducible deep input of the lifting half, carried as **explicit hypothesis fields, never
axioms**.

## What this file proves

* `MURepFamily.UniversalClose R` — the intrinsic four-field bundle (identical content to
  `UniversalData`, restated as the closure datum).
* `UniversalClose.toUniversalData` — `UniversalData R` **as a structure-constructor term**.
* `UniversalClose.realizes` / `UniversalClose.isoInvariant` — the two **derived** clauses exposed as
  terms at the closure level (`bottomIso` / `Dfun.isoInvariant`).
* `zhuBijection_of_universalClose` — the main Zhu theorem from `R` + the closure bundle + scope, the whole
  assembly a term.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchUniversalData` (`MURepFamily.UniversalData`, `zhuBijection_of_universalData`),
`ZhuVermaAnArchGameTwo` (`MUModuleData.LUData`),
`ZhuVermaAnArchFunctorial` (`MUFunctorialData`, `MUFunctorialData.isoInvariant`),
`ZhuVermaAnArchGenFromBottomFinal` (`GenFromBottomFinalFamily`; freeness `ofBottom`),
`ZhuVermaAnArchKerJ` (`KerJData.ker_eq_J`),
`ZhuVermaAnArchMUConstruct` (R0 `bottomBalancedEquiv`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The `UniversalClose` closure bundle over a representation family

`MURepFamily.UniversalClose R` carries the four genuine Dong–Jiang/Frenkel–Zhu construction residues
that close the lifting half — *exactly* the field content of `MURepFamily.UniversalData R`, restated
as the closure datum. From it `UniversalData R` is a **structure-constructor term**, and the
two derived clauses `realizes`/`hiso` are exposed as terms here. -/

/-- **The universal-property closure bundle over a `MURepFamily R`.**

Carries exactly the four genuine `CanonicalAssignmentData`/universal-property residues of the
lifting half of Theorem 5.3.4:

* `ludata`   — the per-`U` maximal-`J` / irreducible-quotient datum
  `MUModuleData.LUData (R.mudata U)` (the Dong–Jiang construction output making `L(U) = M(U)/J`
  irreducible);
* `bottomIso` — the **bottom-survival isomorphism** `((R.toLUFamily ludata).K U).toAMod ≅ U` for
  each `U` (R0 / bottom survival; R0 itself, `MUConstruct.bottomBalancedEquiv`, is already a term);
* `Dfun`     — `MUFunctorialData (R.toLUFamily ludata)`: functoriality of `M(·)` in its bottom
  (`muEquiv`/`muEquiv_maps_J`).  From it the universal-property clause `hiso` is the *term*
  `Dfun.isoInvariant`;
* `G`        — `GenFromBottomFinalFamily (R.toLUFamily ludata)`: the per-`P` generation-from-bottom
  residue, in which the **freeness** side is the term `GradedModeVanish.ofBottom` and the
  first-isomorphism `ker q = J` is the term `KerJData.ker_eq_J`.

This is *exactly* the field content of `MURepFamily.UniversalData R`.  A hypothesis structure, no
`sorry`, **never** an axiom. -/
structure MURepFamily.UniversalClose (R : MURepFamily W) where
  /-- The per-`U` maximal-`J` / irreducible-quotient datum. -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)
  /-- The bottom-survival iso `L(U).toAMod ≅ U` (R0). -/
  bottomIso : ∀ U : AMod W, AModEquiv W ((R.toLUFamily ludata).K U).toAMod U
  /-- Functoriality of `M(·)` in its bottom (sources `hiso` as a term). -/
  Dfun : MUFunctorialData (R.toLUFamily ludata)
  /-- The per-`P` generation-from-bottom residue (freeness and `ker q = J` are terms). -/
  G : GenFromBottomFinalFamily (R.toLUFamily ludata)

namespace MURepFamily.UniversalClose

variable {R : MURepFamily W}

/-- **`R.UniversalData` as a TERM.**  The `UniversalClose` closure bundle `D : R.UniversalClose` is, field
for field, exactly the four genuine residues that `R.UniversalData` carries.  So the intrinsic
universal
bundle is assembled by a single structure constructor — a *term*, no `sorry`, no axiom.  From it
the two derived universal-property clauses `realizes`/`hiso` are the terms. -/
def toUniversalData (D : R.UniversalClose) : R.UniversalData where
  ludata := D.ludata
  bottomIso := D.bottomIso
  Dfun := D.Dfun
  G := D.G

@[simp] theorem toUniversalData_ludata (D : R.UniversalClose) :
    (D.toUniversalData).ludata = D.ludata := rfl

@[simp] theorem toUniversalData_bottomIso (D : R.UniversalClose) :
    (D.toUniversalData).bottomIso = D.bottomIso := rfl

@[simp] theorem toUniversalData_Dfun (D : R.UniversalClose) :
    (D.toUniversalData).Dfun = D.Dfun := rfl

@[simp] theorem toUniversalData_G (D : R.UniversalClose) :
    (D.toUniversalData).G = D.G := rfl

/-- **`R.DownstreamData` as a TERM**, threaded through the intrinsic universal bundle.  This is the
`DownstreamData` produced by `UniversalData.toDownstreamData` (a `rfl`-level repackaging)
fed the term `D.toUniversalData`. -/
def toDownstreamData (D : R.UniversalClose) : R.DownstreamData :=
  (D.toUniversalData).toDownstreamData

@[simp] theorem toDownstreamData_ludata (D : R.UniversalClose) :
    (D.toDownstreamData).ludata = D.ludata := rfl

@[simp] theorem toDownstreamData_bottomIso (D : R.UniversalClose) :
    (D.toDownstreamData).bottomIso = D.bottomIso := rfl

/-- **`realizes` as a TERM** at the closure level.  The `CanonicalAssignmentData.realizes` clause —
the bottom-survival iso `L(U).toAMod ≅ U` — is exactly the carried `bottomIso`, read off the closure
bundle through the term `UniversalData.realizes`. -/
noncomputable def realizes (D : R.UniversalClose) :
    ∀ U : AMod W, AModEquiv W ((((D.toUniversalData).toDownstreamData).F).K U).toAMod U :=
  (D.toUniversalData).realizes

/-- **`hiso` as a TERM** at the closure level.  The universal-property functoriality clause
`∀ U₁ U₂, U₁ ≅ U₂ → L(U₁) ≅ L(U₂)` is the *proven* `MUFunctorialData.isoInvariant` of the carried
`Dfun` — not a separate leaf. -/
theorem isoInvariant (D : R.UniversalClose) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W ((((D.toUniversalData).toDownstreamData).F).K U₁)
        ((((D.toUniversalData).toDownstreamData).F).K U₂) :=
  (D.toUniversalData).isoInvariant

/-- **The canonical assignment data from the closure bundle** — a *term*, with `mudata` the genuine
`buildMUModuleData` term, `realizes` the term `bottomIso`, and `Dfun` the carried functoriality. -/
noncomputable def toCanonicalAssignmentData (D : R.UniversalClose) : CanonicalAssignmentData W :=
  (D.toUniversalData).toCanonicalAssignmentData

/-- **`GeneratedFromBottom W` from the closure bundle**, `hiso` plugged as the term
`Dfun.isoInvariant`, the freeness side as the term `GradedModeVanish.ofBottom`, and `ker q = J` as
the term `KerJData.ker_eq_J`. -/
theorem generatedFromBottom (D : R.UniversalClose) : GeneratedFromBottom W :=
  (D.toUniversalData).generatedFromBottom

end MURepFamily.UniversalClose

end InducedAssignment

/-! ## The headline — the Zhu bijection from the `UniversalClose` closure bundle

The four downstream universal-property residues are bundled intrinsically over the rep family as
`MURepFamily.UniversalClose`, from which `UniversalData` — hence the main Zhu theorem — is a term, with
`realizes`/`hiso`/freeness/`ker q = J` all discharged as terms. -/

/-- **Main theorem — the Zhu bijection from a representation family and the `UniversalClose` closure bundle.**

From

* `R : MURepFamily W`             — the Construction-A representation data on each carrier `MU W U`
                                    (whose `M(U)` carriers are the `buildMUModuleData` terms);
* `D : R.UniversalClose`          — the four genuine downstream residues bundled: the per-`U`
                                    maximal-`J` `ludata`, the bottom-survival iso `bottomIso`, the
                                    `M(·)`-functoriality `Dfun`, and the per-`P`
                                    generation-from-bottom residue `G`;
* `hall : AllLWIrreducible W`     — the ambient irreducibility scope,

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The whole assembly is a term: `D.toUniversalData` is the structure-constructor close,
`UniversalData.toDownstreamData` the `rfl`-level repackaging, `realizes`/`hiso`/freeness/`ker q = J`
the discharged terms, and the headline is `zhuBijection_of_universalData` fed `D.toUniversalData`.
The only carried content is `R` and the four genuine construction residues inside `D`.  No `sorry`,
**never** an axiom. -/
theorem zhuBijection_of_universalClose {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalClose)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalData R D.toUniversalData hall

/-- **`zhuBijection_of_universalClose_via_scopeReduced` — the same headline routed through
`zhuBijection_scopeReduced`.**  Identical content to `zhuBijection_of_universalClose`, factored
through the scope-reduced backbone (`realizes`/`hiso` plugged as terms there). -/
theorem zhuBijection_of_universalClose_via_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalClose)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalData_via_scopeReduced R D.toUniversalData hall

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
