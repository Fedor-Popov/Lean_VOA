/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMULW
import VOA.Modules.ZhuVermaAnArchMUjacobiClose
import VOA.Modules.ZhuVermaAnArchScopeClose

/-!
# The central builder — `M(U)` as a `𝒱`-module **term** (`buildMUModuleData`)

The first step of the construction of the lifting half of Zhu Thm 5.3.4. The headline opaque term
fed into the Zhu bijection is `MUModuleData W U h` (`ZhuVermaAnArchMULW`): the bundled
`WeakModule W (MU W U)` (vacuum/truncation/module-Jacobi 5.3.1b) + grading compatibility
(`L₀ = h + n`) + finiteness + bottom-survival. It is consumed, per bottom `U`, by
`LUFamily.mudata` (`ZhuVermaAnArchUniversal`), hence by `CanonicalAssignmentData.F`
(`ZhuVermaAnArchScopeClose`), hence by `zhuBijection_scopeReduced` whose conclusion is
`Function.Bijective (forwardMap W)` — the main Zhu theorem.

This file constructs `MUModuleData W U h` **as a term**, conditional only on:

* a `V̂`-representation `ρ : VHatRep W (MU W U)` on the carrier (Construction A);
* its field/truncation `ActModeTruncated ρ`;
* a **vacuum-creation datum** `actMode ρ 𝟙 m = if m = -1 then id else 0` (the module form of VA2);
* its **module Jacobi 5.3.1b** `ρ.IsModuleJacobi` (the genuine deep crux — for the *defect quotient*
  carrier it is the **already-proven** term `VHat.VHatRep.isModuleJacobi_quotientRep`,
  `ZhuVermaAnArchMUjacobiClose`; on `MU W U` itself it is carried, **never** an axiom);
* the grading scalar `actMode ρ ω 1 x = (h + n) • x` on `MU.deg n` (5.3.1c, `L0`-eigenvalue);
* finiteness of each level and bottom-nonvanishing (siblings).

## The `VHatRep → WeakModule` bridge

The mode/field correspondence is `Y_M(u,z) = ∑ₙ a₍ₙ₎ z^{-n-1}`, i.e. `(YM u) k = ρ.actMode u (-k-1)`
(`mode (YM u) n = ρ.actMode u n` since `mode f n = f (-n-1)` and `-(-n-1)-1 = n`). This field and
the resulting `WeakModule` are **already built** in `ZhuVermaAnArchMUmod` (`YMof ρ`, `mode_YMof`,
`toWeakModule`, with `vacuum_YMof_iff` reducing 5.3.1a to the mode form). The bridge
`weakModuleOfRep` packages them under the named hypotheses:

* `VacuumCreation ρ` — the carried vacuum-creation datum `𝟙₍ₘ₎ = δ_{m,-1}·id`, precisely the mode
  form of `YMof ρ 𝟙 = 1` (`vacuum_YMof_iff`);
* `truncation` from `ActModeTruncated ρ` (via `mode_YMof`);
* `jacobi` is `ρ.IsModuleJacobi` *verbatim* (`jacobi_field_eq`: `WeakModule.jacobi` and
  `IsModuleJacobi` are the same identity once `mode (YM ·) = actMode ·`).

Everything is structural; no membership/scalar/degree identity is *introduced* here (the only
arithmetic is `-(-n-1)-1 = n`, already discharged in `mode_YMof`), so nothing new requires
Mathematica verification — the deep scalar (`L₀ = h+n`) and combinatorial (Jacobi) content is
carried as the explicit hypotheses listed above, exactly the Construction-A / DJ output.

Everything is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

## References
Dong–Jiang `math/0601626` Prop 3.4–3.5, Thm 4.13; DLM3 §4; H. Li hep-th/9406211 §2;
Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; `WeakModule` (Def 5.3.1a–b),
`ZhuVermaAnArchMUVhat` (`VHatRep`, `actMode`), `ZhuVermaAnArchMUjacobi(Close)` (`ActModeTruncated`,
`IsModuleJacobi`, `isModuleJacobi_quotientRep`).
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

/-! ## The vacuum-creation datum and the `VHatRep → WeakModule` bridge

The state–field correspondence `Y_M(u,z) = ∑ₙ a₍ₙ₎ z^{-n-1}` (`(Y_M u) k = ρ.actMode u (-k-1)`,
`mode (YM u) n = ρ.actMode u n`) and the resulting `WeakModule` are **already built** in
`ZhuVermaAnArchMUmod` as `YMof ρ` / `mode_YMof` / `toWeakModule`, with the vacuum normalization
5.3.1a reduced to its mode form by `vacuum_YMof_iff`. We name that mode form `VacuumCreation` and
package the bridge `weakModuleOfRep` on top of the existing `toWeakModule`. -/

/-- **The vacuum-creation datum** (module mirror of VA2 `Y(𝟙,z)=id`): the vacuum modes are
`𝟙₍ₘ₎ = δ_{m,-1}·id`. This is precisely the mode form of `YMof ρ 𝟙 = 1` (`vacuum_YMof_iff`). For the
genuine induced module it is the action of the loop vacuum mode (`umode` of the vacuum); carried
here as the explicit creation hypothesis on `ρ`. -/
def VacuumCreation (ρ : VHatRep W M) : Prop :=
  ∀ m : ℤ, ρ.actMode W.vacuum m = if m = -1 then (1 : End ℂ M) else 0

/-- **The `WeakModule W M` of a `V̂`-representation** `ρ` satisfying field/truncation, vacuum
creation, and the module Jacobi 5.3.1b — built on the existing `toWeakModule`/`YMof` bridge. Its
field is `YMof ρ`, so `mode (YM u) n = ρ.actMode u n` (`mode_YMof`) and the `WeakModule.jacobi`
field is `ρ.IsModuleJacobi` verbatim (`jacobi_field_eq`). This is the bridge turning the
Construction-A representation into the project's bundled weak-module interface (Def 5.3.1a–b). -/
noncomputable def weakModuleOfRep (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi) : WeakModule W M :=
  toWeakModule ρ ((vacuum_YMof_iff ρ).mpr hvac)
    (fun u x => by
      obtain ⟨N, hN⟩ := htr u x
      exact ⟨N, fun n hn => by rw [mode_YMof]; exact hN n hn⟩)
    hjac

@[simp] theorem weakModuleOfRep_YM (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi) :
    (weakModuleOfRep ρ htr hvac hjac).YM = YMof ρ := rfl

@[simp] theorem weakModuleOfRep_act (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi) (u : 𝒱) (n : ℤ) (x : M) :
    (weakModuleOfRep ρ htr hvac hjac).act u n x = ρ.actMode u n x := by
  rw [WeakModule.act_def, weakModuleOfRep_YM, mode_YMof]

end VHatRep
end VHat

/-! ## The central builder — `MUModuleData` as a term -/

namespace MUModuleData

open VHat VHat.VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **`buildMUModuleData` — `M(U)` as a `𝒱`-module, packaged as the headline term
`MUModuleData W U h`.**

Given a `V̂`-representation `ρ` on the carrier `MU W U` (Construction A) together with the genuine
module data —

* `htr : ActModeTruncated ρ`        — the field/truncation property;
* `hvac : VacuumCreation ρ`         — the vacuum-creation datum `𝟙₍ₘ₎ = δ_{m,-1}` (module VA2);
* `hjac : ρ.IsModuleJacobi`         — the **module Jacobi 5.3.1b** (the deep crux; for the defect
  quotient carrier this is the proven term `isModuleJacobi_quotientRep`);
* `hL0 : ∀ n x, x ∈ MU.deg W U n → ρ.actMode ω 1 x = (h + n) • x` — the grading scalar (5.3.1c);
* `hfin : ∀ n, FiniteDimensional ℂ (MU.deg W U n)` — finiteness of the graded pieces;
* `hbot : MU.deg W U 0 ≠ ⊥`         — bottom nonvanishing —

this is the headline opaque term `MUModuleData W U h`. The `weak` field is the bridge
`weakModuleOfRep ρ …`; `L0_on_deg` is `hL0` translated through `mode_YMof`
(`mode (YM ω) 1 = ρ.actMode ω 1`). No `sorry`, **never** an axiom. -/
noncomputable def buildMUModuleData
    (ρ : VHatRep W (MU W U)) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      ρ.actMode W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) :
    MUModuleData W U h where
  weak := weakModuleOfRep ρ htr hvac hjac
  L0_on_deg := by
    intro n x hx
    rw [show (weakModuleOfRep ρ htr hvac hjac).YM W.conformalVector
          = YMof ρ W.conformalVector from rfl, mode_YMof]
    exact hL0 n x hx
  finrank_deg := hfin
  bottom_ne_bot := hbot

@[simp] theorem buildMUModuleData_weak
    (ρ : VHatRep W (MU W U)) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      ρ.actMode W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) :
    (buildMUModuleData ρ htr hvac hjac hL0 hfin hbot).weak
      = weakModuleOfRep ρ htr hvac hjac := rfl

/-- **The mode action of the built `M(U)` is the representation's `𝒱`-mode action**
(`a₍ₙ₎ · x = ρ.actMode a n x`). -/
@[simp] theorem buildMUModuleData_act
    (ρ : VHatRep W (MU W U)) (htr : ActModeTruncated ρ)
    (hvac : VacuumCreation ρ) (hjac : ρ.IsModuleJacobi)
    (hL0 : ∀ (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
      ρ.actMode W.conformalVector 1 x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MU.deg W U n))
    (hbot : MU.deg W U 0 ≠ ⊥) (a : 𝒱) (n : ℤ) (x : MU W U) :
    (buildMUModuleData ρ htr hvac hjac hL0 hfin hbot).weak.act a n x = ρ.actMode a n x :=
  weakModuleOfRep_act ρ htr hvac hjac a n x

end MUModuleData

/-! ## Headline wiring — `buildMUModuleData ⟹ LUFamily ⟹ CanonicalAssignmentData ⟹ the bijection`

`buildMUModuleData` produces, per bottom `U` (at a chosen lowest weight `hU U`), the headline
`MUModuleData W U (hU U)` that `LUFamily.mudata` consumes. Bundling such per-`U` representation data
with the per-`U` maximal-`J` data (`MUModuleData.LUData`) yields the `LUFamily W` feeding
`CanonicalAssignmentData.F`, hence — with the bottom-survival iso, `M(·)`-functoriality, the per-`P`
residue family, and the ambient irreducibility scope — `zhuBijection_scopeReduced`, whose conclusion
is the main Zhu theorem `Function.Bijective (forwardMap W)`. -/

namespace InducedAssignment

open VHat VHat.VHatRep

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The per-`U` representation data feeding `buildMUModuleData`.** For each bottom `A(𝒱)`-module
`U`, a lowest weight, a `V̂`-representation on `MU W U`, and the module data (truncation, vacuum
creation, module Jacobi, grading scalar, finiteness, bottom-nonvanishing). This is exactly the
Construction-A / DJ output that `buildMUModuleData` turns into `LUFamily.mudata`; a hypothesis
structure, **never** an axiom, with no `sorry`. -/
structure MURepFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The lowest weight of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The Construction-A `V̂`-representation on the carrier `MU W U`. -/
  rho : ∀ U : AMod W, VHatRep W (MU W U)
  /-- Field/truncation of each representation. -/
  htr : ∀ U : AMod W, ActModeTruncated (rho U)
  /-- The vacuum-creation datum (module VA2) of each representation. -/
  hvac : ∀ U : AMod W, VacuumCreation (rho U)
  /-- The module Jacobi 5.3.1b of each representation (the deep crux; for the defect quotient the
  proven term `isModuleJacobi_quotientRep`). -/
  hjac : ∀ U : AMod W, (rho U).IsModuleJacobi
  /-- The grading scalar `L₀ = h + n` on the level-`n` piece (5.3.1c). -/
  hL0 : ∀ (U : AMod W) (n : ℕ) (x : MU W U), x ∈ MU.deg W U n →
    (rho U).actMode W.conformalVector 1 x = ((hU U : ℂ) + n) • x
  /-- Finiteness of each graded piece. -/
  hfin : ∀ (U : AMod W) (n : ℕ), FiniteDimensional ℂ (MU.deg W U n)
  /-- Bottom nonvanishing of each `M(U)`. -/
  hbot : ∀ U : AMod W, MU.deg W U 0 ≠ ⊥

namespace MURepFamily

variable (R : MURepFamily W)

/-- **The headline `MUModuleData` per bottom `U`**, built as a term from the rep family. -/
noncomputable def mudata (U : AMod W) : MUModuleData W U (R.hU U) :=
  MUModuleData.buildMUModuleData (R.rho U) (R.htr U) (R.hvac U) (R.hjac U)
    (R.hL0 U) (R.hfin U) (R.hbot U)

/-- **The `LUFamily W` from the representation family**, given the per-`U` maximal-`J` data. This is
the object `CanonicalAssignmentData.F` consumes. The `mudata` field is produced entirely by
`buildMUModuleData` — `M(U)` as a `𝒱`-module **term**. -/
noncomputable def toLUFamily
    (ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)) : LUFamily W where
  hU := R.hU
  mudata := R.mudata
  ludata := ludata

@[simp] theorem toLUFamily_mudata
    (ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U)) (U : AMod W) :
    (R.toLUFamily ludata).mudata U = R.mudata U := rfl

end MURepFamily

/-- **The canonical assignment data from a representation family** (plus the per-`U` maximal-`J`
data, the bottom-survival iso, and `M(·)`-functoriality). Its `F` is built through
`buildMUModuleData`, so the headline `mudata` is a genuine term, not an opaque hypothesis. -/
noncomputable def MURepFamily.toCanonicalAssignmentData (R : MURepFamily W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((R.toLUFamily ludata).K U).toAMod U)
    (Dfun : MUFunctorialData (R.toLUFamily ludata)) :
    CanonicalAssignmentData W where
  F := R.toLUFamily ludata
  realizes := realizes
  Dfun := Dfun

end InducedAssignment

/-- **Main connection — the Zhu bijection from the representation family.**

Assembling the full lifting half *through* `buildMUModuleData`: from a `MURepFamily W` (the
Construction-A representation data on each carrier `MU W U`), the per-`U` maximal-`J` data, the
bottom-survival iso, `M(·)`-functoriality, the per-`P` residue family, and the ambient
irreducibility scope, the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)` is a **bijection**.
The headline
`MUModuleData` term is produced entirely by `buildMUModuleData` (this file), discharging the opaque
`CanonicalAssignmentData.F.mudata` slot with a genuine `𝒱`-module term. -/
theorem zhuBijection_of_repFamily {W : VertexOperatorAlgebra 𝒱}
    (R : InducedAssignment.MURepFamily W)
    (ludata : ∀ U : AMod W, MUModuleData.LUData (R.mudata U))
    (realizes : ∀ U : AMod W, AModEquiv W ((R.toLUFamily ludata).K U).toAMod U)
    (Dfun : InducedAssignment.MUFunctorialData (R.toLUFamily ludata))
    (hall : InducedAssignment.AllLWIrreducible W)
    (G : InducedAssignment.GenFromBottomFinalFamily (R.toLUFamily ludata)) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_scopeReduced
    (R.toCanonicalAssignmentData ludata realizes Dfun) hall G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
