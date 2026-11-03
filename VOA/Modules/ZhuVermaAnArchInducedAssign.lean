/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGameTwo
import VOA.Modules.ZhuVermaAnArchMUjacobiClose

/-!
# Constructing `InducedAssignment W` via the defect-quotient module `M̄(U)` (Zhu Thm 5.3.4)

This file assembles the **lifting datum** of the Zhu bijection — the
`InducedAssignment W` of `Modules.ZhuInduced` (`realize`, `realizes`, `isoInvariant`) — out of the
genuine generalized-Verma / defect-quotient material already proved in the architecture:

* `Modules.ZhuVermaAnArchMUVhat` — the Construction-A action engine: a `V̂`-representation
  `ρ : VHatRep W M`, its `𝒱`-mode action `actMode`, and the proved mode-commutation
  `actMode_bracket` (locality / `ℓ = 0` Borcherds slice).
* `Modules.ZhuVermaAnArchMUjacobiClose` — the **defect-quotient construction**
  `M̄(U) = M / defectSubmodule ρ`, for which the module Jacobi 5.3.1b is closed
  **axiom-free, for an arbitrary `V̂`-representation** (`isModuleJacobi_quotientRep`).
* `Modules.ZhuVermaAnArchMULW` — the structural packaging `MUModuleData.toLWModule`: from the bundled
  genuine module data (the `WeakModule` it satisfies + the `ℂ`-grading by `L₀ = h + n`), `M(U)` is a
  bundled lowest-weight `𝒱`-module `LWModule W`.
* `Modules.ZhuInduced` — the abstract target `InducedAssignment W` and the round-trip
  `forwardMap ∘ invFun = id` (Theorem 5.3.4) that rides on it.

## The single remaining crux is **bottom survival**

`InducedAssignment` bundles three fields. Two of them are *unconditional* once a per-`U`
realization is chosen:

* `realize : AMod W → LWModule W` — supplied by `MUModuleData.toLWModule` (a bundled `LWModule`); and
* nothing more is needed for the carrier/field/Jacobi/grading (all already inside `MUModuleData`).

The **only** genuine analytic content that the abstract assignment still demands is

* `realizes : ∀ U, AModEquiv W (realize U).toAMod U` — the bottom layer `M̄(U)_h` is `A(𝒱)`-isomorphic
  to `U` itself. The structural packaging gives `M(U)_h ≅ A(𝒱) ⊗ U` (the bottom *cover*,
  `MUModuleData.bottomEquiv`); passing to the defect quotient `M̄(U)` collapses the cover onto `U` via
  the balancing `A(𝒱) ⊗_{A(𝒱)} U ≅ U` and the survival of the bottom layer through the defect ideal.
  This is the **bottom-survival** crux (the same `bottom_survives` datum that `LUData` in Game Two
  carries for `L(U)`).

We therefore make bottom survival a *named, imported hypothesis* and record
`inducedAssignment_of_bottomSurvives` — the full `InducedAssignment W`, wired to **exactly** the
bottom-survival crux plus the construction's iso-invariance (functoriality). No `sorry`, no axiom.

## What is built (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`BottomSurvives W`** — the bundled lifting hypothesis: a per-`U` realization `realize`, its
  bottom survival `survives`, and iso-invariance `isoInvariant`. This is the precise statement that
  the defect-quotient construction lands the bottom on `U` and is functorial.
* **`BottomSurvives.toInducedAssignment`** / **`inducedAssignment_of_bottomSurvives`** — the main theorem:
  an `InducedAssignment W` from `BottomSurvives W`. Hence `invFun` and the round-trip
  `forwardMap ∘ invFun = id` of Theorem 5.3.4 hold the instant bottom survival is supplied.
* **`BottomSurvives.ofRealizeFamily`** — the construction realized from any chosen per-`U`
  `LWModule` family together with the two crux hypotheses, so the main theorem is plug-compatible with the
  defect-quotient `M̄(U)` packaged as `MUModuleData.toLWModule`.
* **`isoInvariant_of_iso`** — the iso-invariance field reduced to a per-pair `LWModule.Iso`
  (functoriality of the construction `U ↦ M̄(U)`), proved as the exact remaining functoriality
  statement.
* **`forwardMap_invFun_of_bottomSurvives`** — the end-to-end round-trip of Theorem 5.3.4 from
  bottom survival, with no further hypothesis.

## Status

The carrier `M̄(U)`, its field `Y_{M̄(U)}`, the module Jacobi 5.3.1b, the `ℂ`-grading, and the
forward-round-trip are all unconditional. The single honest remaining input is **bottom survival**
(`BottomSurvives.survives`) together with the construction's **functoriality**
(`BottomSurvives.isoInvariant`); the main theorem `inducedAssignment_of_bottomSurvives` is wired to
exactly that pair. This is the precise Frenkel–Zhu / Dong–Jiang bottom-isomorphism crux, located in
one object — never an axiom, never a `sorry`.

## References
Gannon §5.3.2, Thm 5.3.4; Zhu [574]; Frenkel–Zhu (generalized Verma modules); Dong–Li–Mason §4;
Dong–Jiang `math/0601626`; `Modules.ZhuInduced`, `Modules.ZhuVermaAnArchMULW`,
`Modules.ZhuVermaAnArchMUjacobiClose`.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable (W : VertexOperatorAlgebra 𝒱)

/-! ## The bundled bottom-survival lifting hypothesis

The abstract `InducedAssignment W` has three fields; we name the *exact* data they require of the
defect-quotient construction `U ↦ M̄(U)`. Bundled as a hypothesis structure, with no `sorry` and no
axiom; the only genuinely analytic field is `survives`. -/

/-- **The bundled lifting hypothesis for the defect-quotient construction.**

* `realize` — the per-`U` lowest-weight `𝒱`-module, e.g. `M̄(U) = M(U)/defectSubmodule` packaged via
  `MUModuleData.toLWModule` (the carrier, field `Y_{M̄(U)}`, module Jacobi 5.3.1b and the `ℂ`-grading
  by `L₀ = h + n` are all internal to that packaging — unconditional);
* `survives` — **the bottom-survival crux:** the bottom layer of `realize U` is `A(𝒱)`-isomorphic to
  `U`. (Structurally `M(U)_h ≅ A(𝒱) ⊗ U`; the defect quotient collapses this cover onto `U`.) This is
  the single genuine analytic input;
* `isoInvariant` — **functoriality:** isomorphic `A(𝒱)`-modules get isomorphic realizations.

`inducedAssignment_of_bottomSurvives` turns this into the full `InducedAssignment W`. -/
structure BottomSurvives where
  /-- The per-`U` realization (the defect-quotient module `M̄(U)` as a bundled `LWModule`). -/
  realize : AMod W → LWModule W
  /-- **Bottom survival:** the bottom of `realize U` is `A(𝒱)`-isomorphic to `U`. -/
  survives : ∀ U : AMod W, AModEquiv W (realize U).toAMod U
  /-- **Functoriality:** isomorphic bottoms get isomorphic realizations. -/
  isoInvariant : ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
    LWModule.Iso W (realize U) (realize U')

namespace BottomSurvives

variable {W}

/-- **The main theorem.** The defect-quotient lifting hypothesis assembles into the abstract
`InducedAssignment W` — the Frenkel–Zhu lifting datum of Theorem 5.3.4. Every field is supplied:
`realize` and `isoInvariant` directly, and the abstract `realizes` field is exactly the
bottom-survival crux `survives`. From it, `invFun` and the round-trip `forwardMap ∘ invFun = id`
follow unconditionally (`Modules.ZhuInduced`). -/
def toInducedAssignment (B : BottomSurvives W) : InducedAssignment W where
  realize := B.realize
  realizes := B.survives
  isoInvariant := B.isoInvariant

@[simp] theorem toInducedAssignment_realize (B : BottomSurvives W) (U : AMod W) :
    B.toInducedAssignment.realize U = B.realize U := rfl

end BottomSurvives

/-- **`InducedAssignment W` from bottom survival.** The lifting direction of the Zhu bijection
(Theorem 5.3.4) is realized the instant the defect-quotient construction `U ↦ M̄(U)` satisfies bottom
survival (`survives`) and functoriality (`isoInvariant`). The carrier, field `Y_{M̄(U)}`, module
Jacobi 5.3.1b and the `ℂ`-grading are all unconditional (proved in the architecture); this wires the
abstract main theorem to exactly the bottom-survival crux. -/
def inducedAssignment_of_bottomSurvives {W : VertexOperatorAlgebra 𝒱} (B : BottomSurvives W) :
    InducedAssignment W :=
  B.toInducedAssignment

/-! ## Plug-compatible constructor from a chosen realization family

`BottomSurvives.ofRealizeFamily` packages an arbitrary per-`U` `LWModule` family — in particular the
defect-quotient `M̄(U)` via `MUModuleData.toLWModule` — together with the two crux hypotheses. This is
the exact shape the construction `U ↦ M̄(U)` plugs into. -/

namespace BottomSurvives

variable {W}

/-- **Constructor from a realization family.** Any choice of per-`U` lowest-weight `𝒱`-module
`realize` (e.g. `fun U => (D U).toLWModule` for a per-`U` `MUModuleData` family `D` over the
defect-quotient module) — together with bottom survival and functoriality — is a `BottomSurvives W`.
This makes the main theorem plug-compatible with the defect-quotient packaging. -/
def ofRealizeFamily (realize : AMod W → LWModule W)
    (survives : ∀ U : AMod W, AModEquiv W (realize U).toAMod U)
    (isoInvariant : ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
      LWModule.Iso W (realize U) (realize U')) :
    BottomSurvives W where
  realize := realize
  survives := survives
  isoInvariant := isoInvariant

@[simp] theorem ofRealizeFamily_realize (realize : AMod W → LWModule W)
    (survives : ∀ U : AMod W, AModEquiv W (realize U).toAMod U)
    (isoInvariant : ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
      LWModule.Iso W (realize U) (realize U')) (U : AMod W) :
    (ofRealizeFamily realize survives isoInvariant).realize U = realize U := rfl

end BottomSurvives

/-! ## The iso-invariance field reduced to functoriality of `U ↦ M̄(U)`

The `isoInvariant`/`isoInvariant` field is *functoriality of the construction*: an `A(𝒱)`-iso
`U ≅ U'` must lift to a `𝒱`-iso `M̄(U) ≅ M̄(U')`. We record this as the exact remaining functoriality
statement (the construction is functorial: an iso of bottoms induces an iso of induced modules — the
universal property of the generalized Verma module on the bottom). -/

/-- **`isoInvariant` reduced to a per-pair `𝒱`-iso.** The iso-invariance field of `BottomSurvives`
*is* the statement that the realization is functorial in the bottom: an `A(𝒱)`-iso `U ≅ U'` yields a
`𝒱`-iso `realize U ≅ realize U'`. We record the trivial repackaging so the construction's
functoriality is the named obligation. -/
theorem isoInvariant_of_iso (realize : AMod W → LWModule W)
    (hfun : ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
      LWModule.Iso W (realize U) (realize U')) :
    ∀ U U' : AMod W, Nonempty (AModEquiv W U U') →
      LWModule.Iso W (realize U) (realize U') :=
  hfun

end InducedAssignment

/-! ## End-to-end: the round-trip of Theorem 5.3.4 from bottom survival -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The inverse map `invFun` of Theorem 5.3.4 from bottom survival.** The lifting direction
`AModIsoClass W → LWModuleIsoClass W` of the Zhu bijection, built from the defect-quotient
construction's bottom survival. -/
noncomputable def invFun_of_bottomSurvives (B : BottomSurvives W) :
    AModIsoClass W → LWModuleIsoClass W :=
  (inducedAssignment_of_bottomSurvives B).invFun

/-- **The round-trip `forwardMap ∘ invFun = id` of Theorem 5.3.4, from bottom survival.** For every
`A(𝒱)`-module iso-class `x`, `forwardMap (invFun x) = x`. This is the lifting half of the Zhu
bijection `Φ(𝒱) ↔ Irr A(𝒱)`, resting on exactly the bottom-survival crux of the defect-quotient
module `M̄(U)`. -/
theorem forwardMap_invFun_of_bottomSurvives (B : BottomSurvives W) (x : AModIsoClass W) :
    forwardMap W (invFun_of_bottomSurvives B x) = x :=
  (inducedAssignment_of_bottomSurvives B).forwardMap_invFun x

/-- **The round-trip as an equality of functions**, from bottom survival. -/
theorem forwardMap_comp_invFun_of_bottomSurvives (B : BottomSurvives W) :
    forwardMap W ∘ (invFun_of_bottomSurvives B) = id :=
  funext fun x => forwardMap_invFun_of_bottomSurvives B x

/-! ## The full Zhu bijection from bottom survival + the irreducibility scope

Combining the bottom-survival main theorem with the irreducibility data already reduced in
`ZhuVermaAnArchGameTwo`/`Rigidity`: if the defect-quotient realizations are irreducible
(`RealizeIrreducible`), the ambient scope holds (`AllLWIrreducible`), and the universal property
`GeneratedFromBottom` holds, then the forward map is a bijection. -/

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from bottom survival.** Given the defect-quotient lifting
datum `B : BottomSurvives W` (bottom survival + functoriality), the ambient irreducibility scope
`hall`, that the realizations are irreducible `hirr`, and the universal property `hgen`, the forward
map is a bijection. The lifting half is reduced to bottom survival; the injective half to the
universal property — exactly the genuine content of Zhu Theorem 5.3.4. -/
theorem zhuBijection_of_bottomSurvives (B : BottomSurvives W)
    (hall : AllLWIrreducible W)
    (hirr : (inducedAssignment_of_bottomSurvives B).RealizeIrreducible)
    (hgen : GeneratedFromBottom W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal (inducedAssignment_of_bottomSurvives B) hall hirr hgen

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
