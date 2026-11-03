/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUModuleDataBuild

/-!
# The genuine `ρ : VHatRep W (MU W U)` + module Jacobi, **on the headline carrier**, via the
  module-iterate residual — bypassing the (false) free-cover truncation

This file proves the **sound** packaging of the deep keystone of Zhu Thm 5.3.4 (the lifting half).
The headline `MURepFamily W` (`ZhuVermaAnArchMUModuleDataBuild`) consumes, per bottom `A(𝒱)`-module
`U`, a genuine `V̂`-representation `rho U : VHatRep W (MU W U)` **on the headline carrier**
`MU W U = ⊕ₙ A_{n,0}(𝒱) ⊗ U`, together with its truncation `htr`, vacuum creation `hvac`, **module
Jacobi 5.3.1b** `hjac`, grading scalar `hL0`, finiteness `hfin` and bottom-nonvanishing `hbot`. The
*deepest* field is `hjac : (rho U).IsModuleJacobi`.

## Why this file: the free-cover truncation is genuinely FALSE

The `transportRep`/`CarrierBridge` chain (`ZhuVermaAnArchCarrierBridge`,
`ZhuVermaAnArchCarrierRho`) discharges `hjac` by **transporting** the defect-quotient Jacobi
`freeRep_defectQuotient_isModuleJacobi` along a `CarrierBridge`, but *every* statement on that route
carries the hypothesis `htr : ActModeTruncated (freeRep W U.carrier)`. That hypothesis is **false**:
`freeRep`'s mode action is `a₍ₘ₎ (e ⊗ x) = (umode W a m * e) ⊗ x`, i.e. left multiplication by the
loop-mode generator `uι (gen W a m)` in the *free* enveloping algebra `U(V̂)` — and left
multiplication by a generator is never eventually `0` (the enveloping algebra has no nilpotency, and
`gen W a m ≠ 0` for all `m` on a homogeneous `a`). So `freeRep` is **not** lower-truncated, and the
transported route is vacuously gated on an unsatisfiable hypothesis.

The honest truncation lives on the **genuine** carrier `MU W U`, where it follows from the
`ℕ`-grading (a raising mode lands in finitely many higher layers): a genuine
`ρ : VHatRep W (MU W U)` *is* truncated. And on a genuine module, the module Jacobi 5.3.1b needs
**no** defect quotient: under truncation it is *equivalent* to the single module-iterate residual
`ModuleIterate ρ` (`isModuleJacobi_iff_iterate`, already proven axiom-clean). So `hjac` is the
**proven term**

  `isModuleJacobi_of_iterate (rho U) (htr U) (hmi U)`

with no transport, no `CarrierBridge`, and no free-cover truncation. The genuine remaining content
is exactly the two honest cruxes **on the headline carrier**: the truncation `htr` (grading) and the
module-iterate residual `hmi` (DLM3 eqs 4.3–4.4 / the genuine DJ residue), both stated as precise
`Prop`s of `rho U`, never an axiom.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `VHat.VHatRep.isModuleJacobi_of_moduleIterate` — alias making the dependency explicit: a
  *truncated* `ρ` with `ModuleIterate ρ` satisfies the module Jacobi 5.3.1b
  (`isModuleJacobi_of_iterate`).
* `MUModuleData.buildMUModuleData_of_iterate` — the headline `MUModuleData W U h` **term** built
  from a genuine truncated `ρ : VHatRep W (MU W U)` satisfying `ModuleIterate`, with `hjac` supplied
  by the module-iterate route (no defect quotient). Its mode action is `ρ.actMode` verbatim.
* `InducedAssignment.GenuineRhoFamily W` — the per-`U` genuine-rep data on the headline carriers,
  carrying the module-iterate residual `hmi` (in place of the carried `hjac`).
* `InducedAssignment.GenuineRhoFamily.toMURepFamily` — the headline `MURepFamily` produced from a
  `GenuineRhoFamily`, with `hjac := isModuleJacobi_of_iterate …` (a **proven term**), `rho`/`htr`/
  `hvac`/`hL0`/`hfin`/`hbot` passed through.
* `zhuBijection_of_genuineRhoFamily` — the main Zhu theorem `Function.Bijective (forwardMap W)` from a
  `GenuineRhoFamily` (plus the downstream named data), assembled through `buildMUModuleData`.

This isolates the keystone's live content into a single precise residual `hmi` (per `U`) on the
genuine carrier, and shows the module Jacobi is free the moment `hmi` holds — with **no** reliance
on the false `ActModeTruncated (freeRep)`.

## References
DLM3 §4 (eqs 4.3–4.4, the iterate/associativity defect); Frenkel–Zhu; Dong–Jiang `math/0601626`
§§2–4; H. Li `hep-th/9406211` §2; Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchMUjacobi`
(`ModuleIterate`, `ActModeTruncated`, `IsModuleJacobi`, `isModuleJacobi_of_iterate`,
`isModuleJacobi_iff_iterate`); `ZhuVermaAnArchMUModuleDataBuild` (`buildMUModuleData`,
`MURepFamily`, `zhuBijection_of_repFamily`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The module Jacobi 5.3.1b from the module-iterate residual (and truncation).** This is a
re-export of `isModuleJacobi_of_iterate` under a name that makes the dependency explicit: a genuine
truncated `V̂`-representation `ρ` whose single associativity/iterate residual `ModuleIterate ρ`
holds (DLM3 eqs 4.3–4.4) satisfies the module Borcherds identity 5.3.1b **directly** — no defect
quotient, no transport along a `CarrierBridge`, and crucially **no** `ActModeTruncated (freeRep)`
(which is false). The only inputs are properties of `ρ` *on its own carrier*. -/
theorem isModuleJacobi_of_moduleIterate (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hmi : ModuleIterate ρ) : ρ.IsModuleJacobi :=
  isModuleJacobi_of_iterate ρ htr hmi

end VHatRep
end VHat

/-! ## The headline `MUModuleData` term from a genuine truncated `ρ` + `ModuleIterate`

`MUModuleData.buildMUModuleData` (`ZhuVermaAnArchMUModuleDataBuild`) consumes a `V̂`-representation
`ρ : VHatRep W (MU W U)` together with `htr`/`hvac`/`hjac`/`hL0`/`hfin`/`hbot`. We supply `hjac` by
the module-iterate route, so the only deep input becomes the residual `hmi : ModuleIterate ρ` on the
genuine carrier `MU W U`. -/

namespace MUModuleData

open VHat VHat.VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **`M(U)` as a `𝒱`-module term from the module-iterate residual.** The headline opaque term
`MUModuleData W U h`, built (via `buildMUModuleData`) from a genuine truncated representation
`ρ : VHatRep W (MU W U)` on the headline carrier whose single associativity residual
`ModuleIterate ρ` holds. The module Jacobi 5.3.1b is the **proven term**
`isModuleJacobi_of_moduleIterate ρ htr hmi` — discharged on the genuine carrier with no defect
quotient and no free-cover truncation. No `sorry`, **never** an axiom. -/
noncomputable def buildMUModuleData_of_iterate
    (ρ : VHatRep W (MU W U)) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hmi : ModuleIterate ρ)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      ρ.actMode W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) :
    MUModuleData W U h :=
  buildMUModuleData ρ htr hvac (isModuleJacobi_of_moduleIterate ρ htr hmi) hL0 hfin hbot

@[simp] theorem buildMUModuleData_of_iterate_act
    (ρ : VHatRep W (MU W U)) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hmi : ModuleIterate ρ)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      ρ.actMode W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) (a : 𝒱) (m : ℤ) (x : MU W U) :
    (buildMUModuleData_of_iterate ρ htr hvac hmi hL0 hfin hbot).weak.act a m x
      = ρ.actMode a m x := by
  rw [buildMUModuleData_of_iterate, buildMUModuleData_act]

end MUModuleData

/-! ## The per-`U` genuine representation family (module-iterate residual) and the main Zhu theorem -/

namespace InducedAssignment

open VHat VHat.VHatRep MUModuleData

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The genuine per-`U` representation data on the headline carriers, via the module-iterate
residual.** For each bottom `A(𝒱)`-module `U`: a lowest weight, a genuine `V̂`-representation
`rho U : VHatRep W (MU W U)` *on the headline carrier*, its truncation `htr` (grading), vacuum
creation `hvac`, the **module-iterate residual** `hmi : ModuleIterate (rho U)` (DLM3 eqs 4.3–4.4 —
the genuine DJ residue content, in place of the carried `hjac`), the grading scalar `hL0`,
finiteness `hfin`, and bottom-nonvanishing `hbot`.

The difference from `MURepFamily`: the module Jacobi field is **replaced** by the module-iterate
residual `hmi`, from which `IsModuleJacobi` is *derived* (no carried Jacobi). A hypothesis
structure, **never** an axiom, with no `sorry`. -/
structure GenuineRhoFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The lowest weight of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The genuine Construction-A `V̂`-representation on the headline carrier `MU W U`. -/
  rho : ∀ U : AMod W, VHatRep W (MU W U)
  /-- Field/truncation of each representation (the grading truncation on the genuine carrier). -/
  htr : ∀ U : AMod W, ActModeTruncated (rho U)
  /-- The vacuum-creation datum (module VA2) of each representation. -/
  hvac : ∀ U : AMod W, VacuumCreation (rho U)
  /-- **The module-iterate residual** `ModuleIterate (rho U)` (DLM3 eqs 4.3–4.4) — the genuine deep
  crux on the headline carrier, *replacing* the carried module Jacobi. -/
  hmi : ∀ U : AMod W, ModuleIterate (rho U)
  /-- The grading scalar `L₀ = h + n` on the level-`n` piece (5.3.1c). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    (rho U).actMode W.conformalVector 1 x = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece. -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

namespace GenuineRhoFamily

variable (R : GenuineRhoFamily W)

/-- **The headline `MURepFamily` produced from a `GenuineRhoFamily`.** Every field is passed
through verbatim *except* the module Jacobi `hjac`, which is the **proven term**
`isModuleJacobi_of_moduleIterate (R.rho U) (R.htr U) (R.hmi U)` — discharged from the
module-iterate residual on the genuine carrier, with no transport, no `CarrierBridge`, and no
free-cover truncation. This is the sound bridge that turns the two honest cruxes (`htr`, `hmi`) on
`MU W U` into the headline representation family. -/
noncomputable def toMURepFamily : MURepFamily W where
  hU := R.hU
  rho := R.rho
  htr := R.htr
  hvac := R.hvac
  hjac := fun U => VHatRep.isModuleJacobi_of_moduleIterate (R.rho U) (R.htr U) (R.hmi U)
  hL0 := R.hL0
  hfin := R.hfin
  hbot := R.hbot

@[simp] theorem toMURepFamily_rho (U : AMod W) : R.toMURepFamily.rho U = R.rho U := rfl

@[simp] theorem toMURepFamily_hU : R.toMURepFamily.hU = R.hU := rfl

@[simp] theorem toMURepFamily_htr (U : AMod W) : R.toMURepFamily.htr U = R.htr U := rfl

end GenuineRhoFamily

end InducedAssignment

/-- **Main connection — the Zhu bijection from a genuine representation family.**

Assembling the full lifting half through the **module-iterate** route: from a `GenuineRhoFamily W`
(the genuine Construction-A representations on the headline carriers `MU W U`, carrying truncation
and the module-iterate residual on each, in place of a carried module Jacobi), the per-`U` maximal-`J`
data, the bottom-survival iso, `M(·)`-functoriality, the ambient irreducibility scope, and the
bottom-generation family, the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.

The headline `MUModuleData` term is produced entirely by `buildMUModuleData`, with its module Jacobi
field supplied by `isModuleJacobi_of_moduleIterate` (the module-iterate route) — so the main theorem rests
on the two honest cruxes (`htr`, `hmi`) *on the genuine carrier*, never on the false
`ActModeTruncated (freeRep)`. No `sorry`, no axiom, no `pbw`. -/
theorem zhuBijection_of_genuineRhoFamily {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.GenuineRhoFamily W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (R.toMURepFamily.mudata U))
    (realizes : ∀ U : AMod W,
      AModEquiv W ((R.toMURepFamily.toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData (R.toMURepFamily.toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily (R.toMURepFamily.toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_repFamily R.toMURepFamily ludata realizes Dfun hall G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
