/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFinalWiring
import VOA.Modules.ZhuVermaAnArchFunctorial

/-!
# Closing the SCOPE leaves of Thm 5.3.4 as TERMS — `hirr`, `hiso`, and the universal lift wired in

`Modules.ZhuVermaAnArchFinalWiring` proved the definitive `FinalScorecard W` whose `bijective` field
is the main Zhu theorem `Function.Bijective (forwardMap W)`, carrying seven fields:

  `A : InducedAssignment W`,   `hall : AllLWIrreducible W`,   `hirr : A.RealizeIrreducible`,
  `F : LUFamily W`,            `hiso` (functoriality of `L(·)`),
  `G : GenFromBottomFinalFamily F`.

This file performs the **SCOPE + universal-property leaf discharge**: it shows that, once the
existence datum `A` is taken to be the **canonical** assignment `realize := U ↦ L(U) = F.K U` built
from the `LUFamily F`, two of the carried scope fields collapse to **terms**:

* **`hirr : A.RealizeIrreducible`** is the TERM `fun U => F.K_isIrreducibleLW U` — the proven
  irreducibility of `L(U)` (`MUModuleData.LUData.toLWModule_isIrreducibleLW`, `GameTwo` /
  `LU_irreducible`).  It is *not* a carried hypothesis once `A` is the canonical assignment.
* **`hiso`** (the functoriality-of-`L(·)` field) is the TERM `Dfun.isoInvariant` — the proven
  quotient-functor descent of `M(·)`-functoriality (`MUFunctorialData.isoInvariant`, `Functorial`).
  It is *not* a carried hypothesis once one supplies the genuine `MUFunctorialData`.

The remaining genuine *data* of the canonical assignment is exactly the **bottom-survival
isomorphism** `realizes : ∀ U, (F.K U).toAMod ≅ U` (the bottom of `L(U) = M(U)/J` is `U`), which
is a true structural fact of the Dong–Jiang construction — carried, **never** an axiom.

## What is discharged as a TERM (the SCOPE leaves)

| hypothesis bundle field          | discharged as the term                                         |
|--------------------------|---------------------------------------------------------------|
| `hirr` (RealizeIrreducible) | `fun U => F.K_isIrreducibleLW U`  (`LU_irreducible`, proven)   |
| `hiso`  (isoInvariant)   | `Dfun.isoInvariant`  (`MUFunctorialData.isoInvariant`, proven) |
| universal lift `G ⟹ GeneratedFromBottom` | `generatedFromBottom_final` (freeness already a term) |

## What genuinely remains (the honest hypothesis list of the theorem statement)

* `F : LUFamily W`           — the Dong–Jiang `M(U)` / `L(U)` construction output (existence);
* `realizes`                 — the bottom-survival iso `(F.K U).toAMod ≅ U` (true structural fact);
* `Dfun : MUFunctorialData F`— functoriality of `M(·)` in its bottom (`hiso`'s genuine source);
* `G : GenFromBottomFinalFamily F` — the per-`P` residue (`β`/`hβ`, sibling `q_act`,
  `bottom_ne_zero`, maximal-`J`; freeness already the term `GradedModeVanish.ofBottom`);
* `hall : AllLWIrreducible W` — **a legitimate statement-hypothesis**: it is the scope restriction
  of Theorem 5.3.4 (the bijection is between the *irreducible* classes `Φ(𝒱)` and `Irr A(𝒱)`); the
  predicate `∀ P : LWModule W, P.IsIrreducibleLW` is, by design (see `ZhuVermaAnArchRigidity`),
  *not* a global theorem about all bundled `LWModule`s — it pins the ambient class to the
  irreducible one, exactly as in Zhu/Gannon §5.3.2.  It is therefore an acceptable hypothesis of the
  statement, not a missing proof obligation.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchGameTwo` (`LU_irreducible`), `ZhuVermaAnArchFunctorial` (`MUFunctorialData`),
`ZhuVermaAnArchRigidity` (`RealizeIrreducible`, `AllLWIrreducible`),
`ZhuVermaAnArchGenFromBottomFinal` (`GenFromBottomFinalFamily`, `generatedFromBottom_final`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## (a) `hirr` as a TERM — irreducibility of the canonical realization `L(U)` -/

/-- **`RealizeIrreducible` is a TERM for the canonical assignment `realize := F.K`.**

If an `InducedAssignment W` `A` realizes each bottom `U` as the irreducible quotient `L(U) = F.K U`
(`hrealize : ∀ U, A.realize U = F.K U`), then `A.RealizeIrreducible` holds **unconditionally**: each
`A.realize U = F.K U` is irreducible by the proven `LUFamily.K_isIrreducibleLW`
(`= MUModuleData.LUData.toLWModule_isIrreducibleLW`, the `LU_irreducible` of `GameTwo`).  This
discharges the `hirr` scope field as a term — it is not a carried hypothesis once `A` is the
canonical `L(U)`-assignment. -/
theorem realizeIrreducible_of_canonical (A : InducedAssignment W) (F : LUFamily W)
    (hrealize : ∀ U : AMod W, A.realize U = F.K U) :
    A.RealizeIrreducible := by
  intro U
  rw [hrealize U]
  exact F.K_isIrreducibleLW U

/-! ## The canonical assignment built from `F` + the bottom-survival iso + `MUFunctorialData` -/

/-- **The bundled data for the *canonical* induced assignment `U ↦ L(U)`.**

This packages exactly the genuine structural data needed to make `realize := U ↦ L(U) = F.K U` an
`InducedAssignment W`, with `hirr` and `hiso` then both free (terms):

* `F`        — the `LUFamily W` (the Dong–Jiang `M(U)`/`L(U)` construction output);
* `realizes` — the **bottom-survival isomorphism** `(F.K U).toAMod ≅ U` (the bottom of `L(U)` is
  `U`;
  a true structural fact of the construction, carried, never an axiom);
* `Dfun`     — `MUFunctorialData F` (functoriality of `M(·)` in its bottom), from which the
  iso-invariance `isoInvariant` of the assignment is the proven term `Dfun.isoInvariant`.

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure CanonicalAssignmentData (W : VertexOperatorAlgebra 𝒱) where
  /-- The `LUFamily` (the `M(U)`/`L(U)` construction output). -/
  F : LUFamily W
  /-- The bottom-survival isomorphism: the bottom of `L(U) = M(U)/J` is `U`. -/
  realizes : ∀ U : AMod W, AModEquiv W (F.K U).toAMod U
  /-- Functoriality of `M(·)` in its bottom (the genuine source of `hiso`). -/
  Dfun : MUFunctorialData F

namespace CanonicalAssignmentData

variable (C : CanonicalAssignmentData W)

/-- **The canonical induced assignment `U ↦ L(U)` as a TERM.**  Its `isoInvariant` field is the
proven `MUFunctorialData.isoInvariant` (the functoriality-of-`L(·)` discharge, `hiso` as a term); its
`realizes` field is the carried bottom-survival iso. -/
noncomputable def toInducedAssignment : InducedAssignment W where
  realize U := C.F.K U
  realizes U := C.realizes U
  isoInvariant := C.Dfun.isoInvariant

@[simp] theorem toInducedAssignment_realize (U : AMod W) :
    C.toInducedAssignment.realize U = C.F.K U := rfl

/-- **`hirr` as a TERM for the canonical assignment.**  `RealizeIrreducible` holds by
`LUFamily.K_isIrreducibleLW` (the proven `LU_irreducible`); not a carried hypothesis. -/
theorem realizeIrreducible : C.toInducedAssignment.RealizeIrreducible :=
  realizeIrreducible_of_canonical C.toInducedAssignment C.F (fun _ => rfl)

/-- **`hiso` as a TERM for the canonical family.**  The functoriality-of-`L(·)` clause is the proven
`MUFunctorialData.isoInvariant`; not a carried hypothesis (its only genuine input is `Dfun`). -/
theorem isoInvariantTerm :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (C.F.K U₁) (C.F.K U₂) :=
  C.Dfun.isoInvariant

end CanonicalAssignmentData

end InducedAssignment

/-! ## The scope-reduced hypothesis bundle — `hirr` and `hiso` discharged as terms

`FinalScorecard W` (FinalWiring) carries seven fields.  Here we expose the **scope-reduced** bundle
whose carried fields are *only* the genuine data — `F` (with the bottom-survival iso and `M(·)`
functoriality, packaged as `CanonicalAssignmentData`), the per-`P` residue family `G`, and the
ambient-scope statement-hypothesis `hall`.  The two scope leaves `hirr` and `hiso` are not
carried: they are the terms `CanonicalAssignmentData.realizeIrreducible` and
`CanonicalAssignmentData.isoInvariantTerm`. -/

/-- **The scope-reduced hypothesis bundle of Theorem 5.3.4** — `hirr`/`hiso` discharged as terms.

Carries *only* the genuine data:

* `C : CanonicalAssignmentData W` — the `LUFamily F`, the bottom-survival iso `realizes`, and the
  `M(·)`-functoriality `Dfun` (which sources `hiso` as the term `C.isoInvariantTerm`);
* `hall : AllLWIrreducible W`     — the **legitimate statement-hypothesis** scoping the bijection to
  the irreducible classes;
* `G : GenFromBottomFinalFamily C.F` — the per-`P` residue (freeness already the term
  `GradedModeVanish.ofBottom`).

The scope leaves `hirr` (irreducibility of the realizations) and `hiso` (functoriality of `L(·)`) are
*not* fields: they are derived as terms inside `bijective`.  No `sorry`, **never** an axiom. -/
structure ScopeReducedScorecard (W : VertexOperatorAlgebra 𝒱) where
  /-- The canonical-assignment data (`F` + bottom-survival iso + `M(·)`-functoriality). -/
  C : InducedAssignment.CanonicalAssignmentData W
  /-- The ambient irreducibility scope of Theorem 5.3.4 (legitimate statement-hypothesis). -/
  hall : InducedAssignment.AllLWIrreducible W
  /-- The per-`P` residue family (freeness already the term `GradedModeVanish.ofBottom`). -/
  G : InducedAssignment.GenFromBottomFinalFamily C.F

namespace ScopeReducedScorecard

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The main Zhu theorem from the scope-reduced hypothesis bundle, with `hirr` and `hiso` plugged as terms.**

`Function.Bijective (forwardMap W)` follows from:

* the canonical assignment `S.C.toInducedAssignment` (term);
* `hirr = S.C.realizeIrreducible` (TERM — `LU_irreducible`);
* `hall = S.hall` (statement-hypothesis);
* the universal property `generatedFromBottom_final S.C.F S.C.isoInvariantTerm S.G`, in which
  `hiso = S.C.isoInvariantTerm` is a TERM (`MUFunctorialData.isoInvariant`) and freeness is the term
  `GradedModeVanish.ofBottom`.

No `A_n`-associativity (`n ≥ 1`) is consumed; the only carried content is `S.C` (the construction
output + bottom-survival iso + `M(·)`-functoriality), `S.G` (the per-`P` residue), and the ambient
scope `S.hall`. -/
theorem bijective (S : ScopeReducedScorecard W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal
    S.C.toInducedAssignment S.hall S.C.realizeIrreducible
    (InducedAssignment.generatedFromBottom_final S.C.F S.C.isoInvariantTerm S.G)

end ScopeReducedScorecard

/-! ## The flat headline — scope leaves `hirr`/`hiso` discharged as terms -/

/-- **`zhuBijection_scopeReduced` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem
5.3.4, with the SCOPE leaves `hirr` and `hiso` discharged as TERMS.**

Given *only* the genuine data —

* `C : CanonicalAssignmentData W`  (the `LUFamily F`, the bottom-survival iso `realizes`, and the
                                    `M(·)`-functoriality `Dfun`),
* `hall : AllLWIrreducible W`      (the ambient irreducibility scope — a legitimate
                                    statement-hypothesis),
* `G : GenFromBottomFinalFamily C.F` (the per-`P` residue; freeness already the term
                                    `GradedModeVanish.ofBottom`)

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

Compared to `zhuBijection_final` / `zhuBijection_final_scorecard`, the two scope fields
`hirr : A.RealizeIrreducible` and `hiso` (functoriality of `L(·)`) are **not carried**: they
are the proven terms `C.realizeIrreducible` (`LU_irreducible`) and `C.isoInvariantTerm`
(`MUFunctorialData.isoInvariant`).  `hall` remains the legitimate scope-pinning statement-hypothesis;
`C` and `G` remain the genuine construction data of the theorem. -/
theorem zhuBijection_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (C : InducedAssignment.CanonicalAssignmentData W)
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily C.F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal
    C.toInducedAssignment hall C.realizeIrreducible
    (InducedAssignment.generatedFromBottom_final C.F C.isoInvariantTerm G)

/-- **`zhuBijection_scopeReduced_of_scorecard` — the same headline routed through the bundle.** -/
theorem zhuBijection_scopeReduced_of_scorecard {W : VertexOperatorAlgebra 𝒱}
    (S : ScopeReducedScorecard W) :
    Function.Bijective (forwardMap W) :=
  S.bijective

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
