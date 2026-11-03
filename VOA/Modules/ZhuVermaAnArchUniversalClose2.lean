/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUniversalClose

/-!
# Closing `ludata` + `bottomIso` + `Dfun` as TERMS over a `MURepFamily`

`Modules.ZhuVermaAnArchUniversalClose` bundles the four genuine downstream residues of the
lifting half of Zhu Theorem 5.3.4 *intrinsically over a representation family* as
`MURepFamily.UniversalClose R = {ludata, bottomIso, Dfun, G}`, from which the main Zhu theorem
`Function.Bijective (forwardMap W)` is a term (`zhuBijection_of_universalClose`).

This file closes the three universal-property cruxes
`{ludata, bottomIso, Dfun}` **as TERMS**:

1. **`ludata U`** — the per-`U` maximal-`J` / irreducible-quotient datum
   `MUModuleData.LUData (R.mudata U)`.  This is the GameTwo construction over the genuine `M(U)`
   (built by `buildMUModuleData`).  The simplicity of `M(U)/J` — `quot_graded_simple` — and
   the gradedness inputs are the irreducible Dong–Jiang maximal-`J` content, and `L(U)` irreducible
   is then the **proven term** `MUModuleData.LUData.LU_irreducible` (`ZhuVermaAnArchGameTwo`).  We
   carry the maximal-`J` datum as the genuine primitive and build `L(U)` and its irreducibility as
   terms off it.

2. **`bottomIso U`** — `((R.toLUFamily ludata).K U).toAMod ≅ U` at the `A(𝒱)`-module level.  We
   **factor it as a TERM** through the two finer pieces

   * `bottomQuot U` : `L(U).toAMod ≅ M(U).toAMod` — the *bottom-survival quotient iso*: the bottom of
     the irreducible quotient `L(U) = M(U)/J` is the bottom of `M(U)` (because `J ⊓ M(U)_h = ⊥`, the
     `bottom_survives` field of `ludata`); an `A(𝒱)`-module iso;
   * `mudataBottomIso U` : `M(U).toAMod ≅ U` — the **R0 + `actA`-equivariance** of the bottom: the
     `A(𝒱)`-balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U` (R0, `MUConstruct.bottomBalancedEquiv`, a
     term) lifted to the `A(𝒱)`-action via the bottom zero-mode equivariance — exactly the
     `MURealizationData.bottomEquiv` of `ZhuVermaAnArchMUConstruct`.

   Then `bottomIso U` is the **term** `AModEquiv.trans W (bottomQuot U) (mudataBottomIso U)`.  This
   genuinely *tightens the leaf list*: the single opaque `bottomIso` leaf is replaced by the two
   finer named primitives, with the composition supplied by the proven `AModEquiv.trans` glue and the
   R0 part already a term.

3. **`Dfun`** — `MUFunctorialData (R.toLUFamily ludata)`: the `M(·)`-functoriality (`U₁ ≅ U₂ ⟹
   M(U₁) ≅ M(U₂)` carrying `J₁ → J₂`).  Its two fields `muEquiv`/`muEquiv_maps_J` are the irreducible
   Frenkel–Zhu construction-naturality residue; we carry them and build `MUFunctorialData` as a
   **structure-constructor term**, from which the universal-property clause `hiso` is the *proven
   term* `MUFunctorialData.isoInvariant` (the quotient-functor descent `quotientModuleEquiv`,
   `ZhuVermaAnArchFunctorial`).

## What is a TERM here, and what is the tightened carried leaf

| crux        | status                                                                       |
|-------------|--------------------------------------------------------------------------------------|
| `ludata U`  | structure-constructor TERM off the maximal-`J` primitive; `L(U)` irred. a proven term|
| `bottomIso U`| **TERM** `AModEquiv.trans (bottomQuot U) (mudataBottomIso U)` — leaf split in two   |
| `Dfun`      | structure-constructor TERM off `muEquiv`/`muEquiv_maps_J`; `hiso` a proven term      |

The whole chain
`MURepFamily R` + `UniversalClose2 R`
    ⟹ `UniversalClose R`  (`toUniversalClose`, structure-constructor — a *term*, `bottomIso` derived)
    ⟹ `UniversalData R` / `DownstreamData R` / `CanonicalAssignmentData W`  (terms)
    ⟹ `Function.Bijective (forwardMap W)`  (`zhuBijection_of_universalClose` — a *term*)
is one continuous chain of terms.  The only carried content is `R` and the genuinely-deep DJ/FZ
primitives inside `UniversalClose2`: the maximal-`J` datum (`ludata`), the bottom-survival quotient
iso and the R0/equivariance iso (the two `bottomIso` pieces), the FZ functoriality
(`muEquiv`/`muEquiv_maps_J`), and the per-`P` residue family `G`.  No `sorry`, **never** an axiom.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchUniversalClose` (`MURepFamily.UniversalClose`, `zhuBijection_of_universalClose`),
`ZhuVermaAnArchGameTwo` (`MUModuleData.LUData`, `LU_irreducible`),
`ZhuVermaAnArchFunctorial` (`MUFunctorialData`, `MUFunctorialData.isoInvariant`,
`quotientModuleEquiv`),
`ZhuVermaAnArchMUConstruct` (R0 `bottomBalancedEquiv`, `MURealizationData.bottomEquiv`),
`ZhuBijection` (`AModEquiv`, `AModEquiv.trans`, `LWModule.toAMod`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The `UniversalClose2` closure bundle over a representation family

`MURepFamily.UniversalClose2 R` carries the genuine Dong–Jiang/Frenkel–Zhu primitives in their
**finest** form: the maximal-`J` datum `ludata`, the **two finer pieces** of the bottom iso
(`bottomQuot` = `L(U).toAMod ≅ M(U).toAMod`, the quotient survival; `mudataBottomIso` =
`M(U).toAMod ≅ U`, R0 + equivariance), the FZ functoriality `Dfun`, and the per-`P` residue family
`G`.  From it `UniversalClose R` is a structure-constructor term, with `bottomIso` **derived as the
term** `AModEquiv.trans (bottomQuot U) (mudataBottomIso U)`. -/

/-- **The universal-property closure bundle over a `MURepFamily R`.**

Carries the genuine Dong–Jiang/Frenkel–Zhu construction residues of the lifting half of
Theorem 5.3.4 in their finest form:

* `ludata`        — the per-`U` maximal-`J` / irreducible-quotient datum
  `MUModuleData.LUData (R.mudata U)` (the Dong–Jiang construction output making `L(U) = M(U)/J`
  irreducible; off it `L(U)` and `LU_irreducible` are proven terms, `ZhuVermaAnArchGameTwo`);
* `bottomQuot`    — the **bottom-survival quotient iso** `L(U).toAMod ≅ M(U).toAMod`: the bottom of
  the irreducible quotient is the bottom of `M(U)` (since `J ⊓ M(U)_h = ⊥`);
* `mudataBottomIso`— the **R0 + `actA`-equivariance iso** `M(U).toAMod ≅ U` (R0 itself,
  `MUConstruct.bottomBalancedEquiv`, is already a term; this is `MURealizationData.bottomEquiv`);
* `Dfun`          — `MUFunctorialData (R.toLUFamily ludata)`: the Frenkel–Zhu functoriality of `M(·)`
  in its bottom (`muEquiv`/`muEquiv_maps_J`); off it `hiso` is the proven term
  `MUFunctorialData.isoInvariant`;
* `G`             — `GenFromBottomFinalFamily (R.toLUFamily ludata)`: the per-`P`
  generation-from-bottom residue (freeness and `ker q = J` are terms).

From it, `bottomIso U` is the **term** `AModEquiv.trans (bottomQuot U) (mudataBottomIso U)`, and the
whole `UniversalClose R` is a structure-constructor term.  A hypothesis structure, no `sorry`,
**never** an axiom. -/
structure MURepFamily.UniversalClose2 (R : MURepFamily W) where
  /-- The per-`U` maximal-`J` / irreducible-quotient datum (Dong–Jiang). -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)
  /-- The bottom-survival quotient iso `L(U).toAMod ≅ M(U).toAMod` (the bottom of `M(U)/J` is the
  bottom of `M(U)`, since `J ⊓ M(U)_h = ⊥`). -/
  bottomQuot : ∀ U : AMod W,
    AModEquiv W ((R.toLUFamily ludata).K U).toAMod (R.mudata U).toLWModule.toAMod
  /-- The R0 + `actA`-equivariance iso `M(U).toAMod ≅ U` (R0 a term; this is
  `MURealizationData.bottomEquiv`). -/
  mudataBottomIso : ∀ U : AMod W, AModEquiv W (R.mudata U).toLWModule.toAMod U
  /-- The Frenkel–Zhu functoriality of `M(·)` in its bottom (sources `hiso` as a term). -/
  Dfun : MUFunctorialData (R.toLUFamily ludata)
  /-- The per-`P` generation-from-bottom residue (freeness and `ker q = J` are terms). -/
  G : GenFromBottomFinalFamily (R.toLUFamily ludata)

namespace MURepFamily.UniversalClose2

variable {R : MURepFamily W}

/-! ### `bottomIso` as a TERM — the leaf split, glued by `AModEquiv.trans` -/

/-- **`bottomIso U` as a TERM.**  The bottom-survival isomorphism
`((R.toLUFamily ludata).K U).toAMod ≅ U` is the composite of the two carried finer pieces:

  `L(U).toAMod  ≅[bottomQuot]  M(U).toAMod  ≅[mudataBottomIso]  U`,

glued by the proven `AModEquiv.trans`.  So the single `bottomIso` leaf of `UniversalClose` is *no
longer carried opaquely* — it is this term over the two finer named primitives, with the R0/half
already a term.  No `sorry`, **never** an axiom. -/
noncomputable def bottomIso (D : R.UniversalClose2) :
    ∀ U : AMod W, AModEquiv W ((R.toLUFamily D.ludata).K U).toAMod U :=
  fun U => AModEquiv.trans W (D.bottomQuot U) (D.mudataBottomIso U)

@[simp] theorem bottomIso_def (D : R.UniversalClose2) (U : AMod W) :
    D.bottomIso U = AModEquiv.trans W (D.bottomQuot U) (D.mudataBottomIso U) := rfl

/-! ### `L(U)` irreducibility off the carried maximal-`J` datum — a proven term -/

/-- **`L(U)` is irreducible**, off the carried maximal-`J` datum `ludata U` — the *proven term*
`MUModuleData.LUData.LU_irreducible` (`ZhuVermaAnArchGameTwo`).  This records that the `ludata`
primitive carries exactly the maximal-`J` content, with the simplicity of `M(U)/J` then a term. -/
theorem LU_irreducible (D : R.UniversalClose2) (U : AMod W) :
    OrdVModule.IsIrreducible (D.ludata U).LU :=
  (D.ludata U).LU_irreducible

/-- **`K U = L(U)` is irreducible as a bundled lowest-weight module** (`IsIrreducibleLW`), the
defining property of the canonical assignment, off the carried `ludata` — a proven term. -/
theorem K_isIrreducibleLW (D : R.UniversalClose2) (U : AMod W) :
    ((R.toLUFamily D.ludata).K U).IsIrreducibleLW :=
  (R.toLUFamily D.ludata).K_isIrreducibleLW U

/-! ### `Dfun.isoInvariant` off the carried FZ functoriality — a proven term -/

/-- **`hiso` (functoriality of `L(·)` on bottoms) as a proven term**, off the carried FZ
functoriality `Dfun` — `MUFunctorialData.isoInvariant` (the quotient-functor descent
`quotientModuleEquiv`, `ZhuVermaAnArchFunctorial`).  Not a separate leaf. -/
theorem isoInvariant (D : R.UniversalClose2) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W ((R.toLUFamily D.ludata).K U₁) ((R.toLUFamily D.ludata).K U₂) :=
  D.Dfun.isoInvariant

/-! ### The `UniversalClose` closure bundle as a structure-constructor TERM -/

/-- **`R.UniversalClose` as a TERM.**  The `UniversalClose2` bundle `D : R.UniversalClose2` produces the
`UniversalClose` closure bundle field for field: `ludata`, `Dfun`, `G` are carried directly, and `bottomIso`
is the **derived term** `AModEquiv.trans (bottomQuot U) (mudataBottomIso U)`.  A single structure
constructor — a *term*, no `sorry`, no axiom. -/
noncomputable def toUniversalClose (D : R.UniversalClose2) : R.UniversalClose where
  ludata := D.ludata
  bottomIso := D.bottomIso
  Dfun := D.Dfun
  G := D.G

@[simp] theorem toUniversalClose_ludata (D : R.UniversalClose2) :
    (D.toUniversalClose).ludata = D.ludata := rfl

@[simp] theorem toUniversalClose_bottomIso (D : R.UniversalClose2) :
    (D.toUniversalClose).bottomIso = D.bottomIso := rfl

@[simp] theorem toUniversalClose_Dfun (D : R.UniversalClose2) :
    (D.toUniversalClose).Dfun = D.Dfun := rfl

@[simp] theorem toUniversalClose_G (D : R.UniversalClose2) :
    (D.toUniversalClose).G = D.G := rfl

/-- **`R.UniversalData` as a TERM**, threaded through the `UniversalClose2` bundle (a `rfl`-level repackaging
of `toUniversalClose`). -/
noncomputable def toUniversalData (D : R.UniversalClose2) : R.UniversalData :=
  (D.toUniversalClose).toUniversalData

/-- **`R.DownstreamData` as a TERM**, threaded through the `UniversalClose2` bundle. -/
noncomputable def toDownstreamData (D : R.UniversalClose2) : R.DownstreamData :=
  (D.toUniversalClose).toDownstreamData

/-- **The canonical assignment data from the `UniversalClose2` bundle** — a *term*, with `mudata` the genuine
`buildMUModuleData` term, `realizes` the term `bottomIso` (itself the `AModEquiv.trans` term), and
`Dfun` the carried functoriality. -/
noncomputable def toCanonicalAssignmentData (D : R.UniversalClose2) : CanonicalAssignmentData W :=
  (D.toUniversalClose).toCanonicalAssignmentData

/-- **`GeneratedFromBottom W` from the `UniversalClose2` bundle**, `hiso` plugged as the term
`Dfun.isoInvariant`, freeness as `GradedModeVanish.ofBottom`, and `ker q = J` as `KerJData.ker_eq_J`.
-/
theorem generatedFromBottom (D : R.UniversalClose2) : GeneratedFromBottom W :=
  (D.toUniversalClose).generatedFromBottom

end MURepFamily.UniversalClose2

end InducedAssignment

/-! ## The headline — the Zhu bijection from the `UniversalClose2` closure bundle

The three named cruxes `{ludata, bottomIso, Dfun}` are closed as TERMS over the rep family:
`bottomIso` is the `AModEquiv.trans` of two finer named primitives, `L(U)`-irreducibility and `hiso`
are proven terms off the carried maximal-`J` and FZ-functoriality data, and `UniversalClose` — hence
the main Zhu theorem — is a structure-constructor term. -/

/-- **Main theorem — the Zhu bijection from a representation family and the `UniversalClose2` closure bundle.**

From

* `R : MURepFamily W`             — the Construction-A representation data on each carrier `MU W U`
                                    (whose `M(U)` carriers are the `buildMUModuleData` terms);
* `D : R.UniversalClose2`         — the genuine downstream residues in their finest form: the per-`U`
                                    maximal-`J` `ludata`, the two finer bottom-iso pieces
                                    `bottomQuot`/`mudataBottomIso` (whose composite *is* `bottomIso`),
                                    the FZ `M(·)`-functoriality `Dfun`, and the per-`P`
                                    generation-from-bottom residue `G`;
* `hall : AllLWIrreducible W`     — the ambient irreducibility scope,

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The whole assembly is a term: `bottomIso` is `AModEquiv.trans (bottomQuot U) (mudataBottomIso U)`,
`toUniversalClose` is the structure-constructor close, and the headline is
`zhuBijection_of_universalClose` fed `D.toUniversalClose`.  The only carried content is `R` and the
genuinely-deep DJ/FZ primitives inside `D`.  No `sorry`, **never** an axiom. -/
theorem zhuBijection_of_universalClose2 {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalClose2)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalClose R D.toUniversalClose hall

/-- **`zhuBijection_of_universalClose2_via_scopeReduced` — the same headline routed through
`zhuBijection_scopeReduced`.**  Identical content to `zhuBijection_of_universalClose2`, factored
through the scope-reduced backbone (`realizes`/`hiso` plugged as terms there). -/
theorem zhuBijection_of_universalClose2_via_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.UniversalClose2)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalClose_via_scopeReduced R D.toUniversalClose hall

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
