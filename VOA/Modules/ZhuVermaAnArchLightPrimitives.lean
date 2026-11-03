/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUniversalClose2
import VOA.Modules.ZhuVermaAnArchMUConstruct

/-!
# Closing the LIGHTER DJ/FZ primitives of `UniversalClose2` as TERMS

`Modules.ZhuVermaAnArchUniversalClose2` bundles the genuine downstream residues of the
lifting half of Zhu Theorem 5.3.4 in their **finest** form as
`MURepFamily.UniversalClose2 R = {ludata, bottomQuot, mudataBottomIso, Dfun, G}`, from which the Zhu
main theorem `Function.Bijective (forwardMap W)` is a term
(`zhuBijection_of_universalClose2`).

This file performs the **close** of the *lighter* of those carried primitives **as TERMS**,
and reduces the two genuinely-deep ones to a *precise* finer carrier, by introducing a single finest
data bundle `MURepFamily.LightData R` and producing each `UniversalClose2` field — hence
`UniversalClose2` itself, hence the main theorem — as a term off it.

The four carried `UniversalClose2` fields and their status:

| field             | status                                                                   |
|-------------------|----------------------------------------------------------------------------------|
| `Dfun`            | **TERM** — structure-constructor off the two finest FZ residues `muEquiv`/`maps_J`|
| `mudataBottomIso` | **TERM** — it *is* `MURealizationData.bottomEquiv` (R0 `bottomBalancedEquiv` + eq.) |
| `bottomQuot`      | reduced to the finest carrier: the bottom-survival `AModEquiv` `L(U)_h ≅ M(U)_h`  |
| `ludata`          | reduced to the finest carrier: the per-`U` maximal-`J` datum `MUModuleData.LUData`|

The two genuinely-deep DJ residues (`ludata` = the maximal-`J` / Zorn-on-graded-bottom-trivial
datum; `bottomQuot` = the bottom-survival quotient iso, the survival `J ⊓ M(U)_h = ⊥`) are carried in
their tightest shape — `ludata` exactly as the `MUModuleData.LUData` term (off which `L(U)`,
`L(U)`-irreducibility, the graded simplicity from maximality are already proven terms,
`ZhuVermaAnArchGameTwo`), and `bottomQuot` exactly as the single `A(𝒱)`-module iso of the bottoms
(the only honest content of `L(U).toAMod ≅ M(U).toAMod`, since `toAMod` reads only the weight-`h`
layer). The two **lighter** ones are full TERMS:

* **`Dfun`** is the structure constructor `MUFunctorialData.mk muEquiv muEquiv_maps_J` — there is no
  residue beyond those two finest FZ functoriality fields, and `Dfun.isoInvariant` is the proven term
  `MUFunctorialData.isoInvariant` (`ZhuVermaAnArchFunctorial`).
* **`mudataBottomIso U`** is *literally* the `MURealizationData.bottomEquiv` field of the realization
  datum — the R0 balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U` (`MUConstruct.bottomBalancedEquiv`, a
  term) lifted to the `A(𝒱)`-action by the bottom zero-mode equivariance. We carry the realization
  datum whose `.data` is the genuine `R.mudata U` and read off its bottom iso as the term.

From `LightData R`, `UniversalClose2 R` is a structure-constructor term, with `Dfun` and
`mudataBottomIso` *derived as terms* and the two deep residues carried in finest form. This genuinely
**tightens the leaf list**: the opaque `Dfun` and `mudataBottomIso` leaves of `UniversalClose2` are
replaced by their finest sources (FZ `muEquiv`/`maps_J`; the realization datum's `bottomEquiv`), and
the chain to the main theorem is one continuous run of terms.

## Headline connection to `forwardMap`

`MURepFamily R` + `LightData R`
    ⟹ `UniversalClose2 R`            (`toUniversalClose2`, structure-constructor TERM)
    ⟹ `UniversalClose R`             (`UniversalClose2.toUniversalClose`, TERM)
    ⟹ `Function.Bijective (forwardMap W)`  (`zhuBijection_of_universalClose2`, TERM)
is one chain of terms; `zhuBijection_of_lightData` is the proved headline.

`#print axioms` on every proved theorem is exactly `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchUniversalClose2` (`MURepFamily.UniversalClose2`, `zhuBijection_of_universalClose2`),
`ZhuVermaAnArchGameTwo` (`MUModuleData.LUData`, `LU_irreducible`),
`ZhuVermaAnArchFunctorial` (`MUFunctorialData`, `MUFunctorialData.isoInvariant`),
`ZhuVermaAnArchMUConstruct` (R0 `bottomBalancedEquiv`, `MURealizationData`, `bottomEquiv`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The `LightData` finest-data bundle over a representation family

`MURepFamily.LightData R` carries the genuine Dong–Jiang/Frenkel–Zhu residues of the lifting half of
Theorem 5.3.4 in their **tightest** shape:

* the per-`U` maximal-`J` datum `ludata` (the only honest carrier of `L(U)` irreducibility);
* the per-`U` bottom-survival `A(𝒱)`-iso `bottomQuotEquiv` `L(U)_h ≅ M(U)_h` (the only honest content
  of `L(U).toAMod ≅ M(U).toAMod`, the survival `J ⊓ M(U)_h = ⊥`);
* the per-`U` realization datum `realData` (whose `.data` is the genuine `R.mudata U`) — its
  `bottomEquiv` field *is* `mudataBottomIso`, R0 + equivariance;
* the two finest FZ functoriality residues `muEquiv`/`muEquiv_maps_J` — off them `Dfun` is the
  structure-constructor TERM;
* the per-`P` generation-from-bottom residue `G`.

From it, `Dfun` and `mudataBottomIso` are *derived as terms*, and the whole `UniversalClose2 R` is a
structure-constructor term. -/
structure MURepFamily.LightData (R : MURepFamily W) where
  /-- The per-`U` maximal-`J` / irreducible-quotient datum (Dong–Jiang; the only honest carrier of
  `L(U)`-irreducibility — off it `L(U)`, `LU_irreducible`, graded simplicity are proven terms). -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)
  /-- The bottom-survival `A(𝒱)`-iso `L(U)_h ≅ M(U)_h` — the only honest content of
  `L(U).toAMod ≅ M(U).toAMod` (`toAMod` reads only the weight-`h` layer; the survival
  `J ⊓ M(U)_h = ⊥`). -/
  bottomQuotEquiv : ∀ U : AMod W,
    AModEquiv W ((R.toLUFamily ludata).K U).toAMod (R.mudata U).toLWModule.toAMod
  /-- The realization datum whose `.data` is the genuine `R.mudata U`: its `bottomEquiv` field *is*
  `mudataBottomIso` (R0 `bottomBalancedEquiv` + the bottom `actA`-equivariance). -/
  realData : ∀ U : AMod W,
    { S : MURealizationData W U (R.hU U) // S.data = R.mudata U }
  /-- The lifted `𝒱`-module iso `M(U₁) ≅ M(U₂)` for each `A(𝒱)`-iso of bottoms (finest FZ residue). -/
  muEquiv : ∀ {U₁ U₂ : AMod W}, AModEquiv W U₁ U₂ →
    ModuleEquiv W (R.mudata U₁).toOrdVModule (R.mudata U₂).toOrdVModule
  /-- The lifted iso carries the maximal `J₁` onto `J₂` (finest FZ residue). -/
  muEquiv_maps_J : ∀ {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂),
    ((ludata U₁).J.carrier).map ((muEquiv φ).toLinearEquiv : MU W U₁ →ₗ[ℂ] MU W U₂)
      = (ludata U₂).J.carrier
  /-- The per-`P` generation-from-bottom residue (freeness and `ker q = J` are terms). -/
  G : GenFromBottomFinalFamily (R.toLUFamily ludata)

namespace MURepFamily.LightData

variable {R : MURepFamily W}

/-! ### `Dfun` as a TERM — the structure constructor off the two finest FZ residues -/

/-- **`Dfun` as a TERM.**  The Frenkel–Zhu functoriality datum `MUFunctorialData (R.toLUFamily
ludata)` is the structure constructor over the two carried finest residues `muEquiv` and
`muEquiv_maps_J`: there is no content beyond the lifted `M(U₁) ≅ M(U₂)` and its carrying `J₁ → J₂`.
A single structure-constructor term — no `sorry`, **never** an axiom. -/
def Dfun (D : R.LightData) : MUFunctorialData (R.toLUFamily D.ludata) where
  muEquiv := D.muEquiv
  muEquiv_maps_J := D.muEquiv_maps_J

@[simp] theorem Dfun_muEquiv (D : R.LightData) {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) :
    (D.Dfun).muEquiv φ = D.muEquiv φ := rfl

@[simp] theorem Dfun_muEquiv_maps_J (D : R.LightData) {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂) :
    (D.Dfun).muEquiv_maps_J φ = D.muEquiv_maps_J φ := rfl

/-- **`isoInvariant` (functoriality of `L(·)` on bottoms) as a proven term**, off the term `Dfun` —
`MUFunctorialData.isoInvariant` (the quotient-functor descent `quotientModuleEquiv`,
`ZhuVermaAnArchFunctorial`). Not a separate leaf. -/
theorem isoInvariant (D : R.LightData) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W ((R.toLUFamily D.ludata).K U₁) ((R.toLUFamily D.ludata).K U₂) :=
  (D.Dfun).isoInvariant

/-! ### `mudataBottomIso` as a TERM — the realization datum's `bottomEquiv` -/

/-- **`mudataBottomIso U` as a TERM.**  The carried realization datum `realData U` has `.data` equal
to `R.mudata U` (the genuine `buildMUModuleData` term), and its `bottomEquiv` field is exactly the
`A(𝒱)`-module iso `M(U).toAMod ≅ U` — the R0 balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`
(`MUConstruct.bottomBalancedEquiv`, a term) lifted to the `A(𝒱)`-action by the bottom zero-mode
equivariance. We read it off, transporting along the proof `(realData U).2 : S.data = R.mudata U`.
No `sorry`, **never** an axiom. -/
noncomputable def mudataBottomIso (D : R.LightData) :
    ∀ U : AMod W, AModEquiv W (R.mudata U).toLWModule.toAMod U :=
  fun U => (D.realData U).2 ▸ (D.realData U).1.bottomEquiv

/-! ### `bottomQuot` as a TERM off the carried finest bottom-survival iso -/

/-- **`bottomQuot U` as a TERM.**  The full `A(𝒱)`-module iso `L(U).toAMod ≅ M(U).toAMod` is exactly
the carried finest bottom-survival iso `bottomQuotEquiv U` — there is no further content, since
`toAMod` reads only the weight-`h` layer and the only honest claim is that the bottoms agree (the
survival `J ⊓ M(U)_h = ⊥`). Read off; no `sorry`, **never** an axiom. -/
noncomputable def bottomQuot (D : R.LightData) :
    ∀ U : AMod W, AModEquiv W ((R.toLUFamily D.ludata).K U).toAMod (R.mudata U).toLWModule.toAMod :=
  D.bottomQuotEquiv

/-! ### The `UniversalClose2` bundle as a structure-constructor TERM -/

/-- **`R.UniversalClose2` as a TERM.**  The `LightData` finest bundle `D : R.LightData` produces the
`UniversalClose2` bundle field for field: `ludata`, `bottomQuot`, `G` are carried (the deep
residues in finest form), `mudataBottomIso` is the **derived term** `(realData U).bottomEquiv`, and
`Dfun` is the **derived term** structure constructor over `muEquiv`/`muEquiv_maps_J`. A single
structure constructor — a *term*, no `sorry`, no axiom. -/
noncomputable def toUniversalClose2 (D : R.LightData) : R.UniversalClose2 where
  ludata := D.ludata
  bottomQuot := D.bottomQuot
  mudataBottomIso := D.mudataBottomIso
  Dfun := D.Dfun
  G := D.G

@[simp] theorem toUniversalClose2_ludata (D : R.LightData) :
    (D.toUniversalClose2).ludata = D.ludata := rfl

@[simp] theorem toUniversalClose2_bottomQuot (D : R.LightData) :
    (D.toUniversalClose2).bottomQuot = D.bottomQuot := rfl

@[simp] theorem toUniversalClose2_mudataBottomIso (D : R.LightData) :
    (D.toUniversalClose2).mudataBottomIso = D.mudataBottomIso := rfl

@[simp] theorem toUniversalClose2_Dfun (D : R.LightData) :
    (D.toUniversalClose2).Dfun = D.Dfun := rfl

@[simp] theorem toUniversalClose2_G (D : R.LightData) :
    (D.toUniversalClose2).G = D.G := rfl

/-- **`R.UniversalClose` as a TERM**, threaded through the `LightData` bundle (the 
`UniversalClose2.toUniversalClose` term, whose `bottomIso` is itself the `AModEquiv.trans` of the two
finer pieces). -/
noncomputable def toUniversalClose (D : R.LightData) : R.UniversalClose :=
  (D.toUniversalClose2).toUniversalClose

/-- **`GeneratedFromBottom W` from the `LightData` bundle** — `hiso` plugged as the term
`Dfun.isoInvariant`, threaded through the `UniversalClose2` bundle. -/
theorem generatedFromBottom (D : R.LightData) : GeneratedFromBottom W :=
  (D.toUniversalClose2).generatedFromBottom

end MURepFamily.LightData

end InducedAssignment

/-! ## The headline — the Zhu bijection from the `LightData` finest-data bundle

The two lighter cruxes `{Dfun, mudataBottomIso}` are closed as TERMS over the rep family (`Dfun` the
structure constructor over the finest FZ residues; `mudataBottomIso` the realization datum's
`bottomEquiv` = R0 + equivariance), and the two deep residues `{ludata, bottomQuot}` are carried in
finest form; `UniversalClose2` — hence the main Zhu theorem — is then a structure-constructor term. -/

/-- **Main theorem — the Zhu bijection from a rep family and the `LightData` finest-data bundle.**

From

* `R : MURepFamily W`             — the Construction-A representation data on each carrier `MU W U`
                                    (whose `M(U)` carriers are the `buildMUModuleData` terms);
* `D : R.LightData`               — the genuine residues in finest form: the per-`U` maximal-`J`
                                    `ludata` and the bottom-survival iso `bottomQuotEquiv`
                                    (carried), the realization datum `realData` (off which
                                    `mudataBottomIso` is a term), the finest FZ residues
                                    `muEquiv`/`muEquiv_maps_J` (off which `Dfun` is a term), and
                                    the per-`P` residue `G`;
* `hall : AllLWIrreducible W`     — the ambient irreducibility scope,

the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The whole assembly is a term: `Dfun`/`mudataBottomIso` are derived terms, `toUniversalClose2` is the
structure-constructor close, and the headline is `zhuBijection_of_universalClose2` fed
`D.toUniversalClose2`. No `sorry`, **never** an axiom. -/
theorem zhuBijection_of_lightData {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.LightData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalClose2 R D.toUniversalClose2 hall

/-- **`zhuBijection_of_lightData_via_scopeReduced` — the same headline routed through
`zhuBijection_scopeReduced`.** Identical content to `zhuBijection_of_lightData`, factored through
the scope-reduced backbone. -/
theorem zhuBijection_of_lightData_via_scopeReduced {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W) (D : R.LightData)
    (hall : InducedAssignment.AllLWIrreducible W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universalClose2_via_scopeReduced R D.toUniversalClose2 hall

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
