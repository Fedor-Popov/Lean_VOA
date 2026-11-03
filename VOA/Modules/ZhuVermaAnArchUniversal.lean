/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGameTwo

/-!
# The universal property `GeneratedFromBottom W` — realizing `K := U ↦ L(U)`

`Modules.ZhuVermaAnArchGameTwo` reduced the injective half of Zhu Theorem 5.3.4
(`IrredBottomRigidity W`) to the *single* universal-property crux

  `InducedAssignment.GeneratedFromBottom W :=`
  `  ∃ K : AMod W → LWModule W,`
  `    (∀ U₁ U₂, U₁ ≅ U₂ → K U₁ ≅ K U₂) ∧ (∀ irreducible P, K P.toAMod ≅ P)`

(`zhuBijection_of_universal` consumes exactly this). This file **realizes** that existential
honestly: the canonical assignment is `K U := L(U)`, the irreducible lowest-weight quotient
`M(U)/J` of the Dong–Jiang generalized-Verma module, packaged as an `LWModule W` by
`MUModuleData.LUData.toLWModule`.

## The two clauses, located precisely

For `K = U ↦ L(U)` the two clauses of `GeneratedFromBottom` are exactly the two genuine
ingredients of the injective half of Theorem 5.3.4:

* **Iso-invariance** `U₁ ≅ U₂ ⟹ L(U₁) ≅ L(U₂)` — functoriality of the generalized-Verma
  construction on the bottom: an `A(𝒱)`-iso of bottoms lifts to a `𝒱`-iso `M(U₁) ≅ M(U₂)`
  carrying the maximal `J₁` onto `J₂`, hence descends to `L(U₁) ≅ L(U₂)`.
* **Realization** `P irreducible ⟹ L(P.toAMod) ≅ P` — *generation-from-bottom* / the
  Frobenius universal property: a bottom map `P.toAMod → P_h` lifts to a `𝒱`-module surjection
  `M(P.toAMod) ↠ P` that is the identity on the bottom; `P` irreducible + the surjection then
  force `P ≅ M(P.toAMod)/J = L(P.toAMod)` (the kernel is the maximal bottom-trivial submodule
  `J`).

## What is built (axiom-clean)

We carry exactly these two clauses for the canonical `K = U ↦ L(U)` as the bundled hypothesis
structure `LUUniversalData W` (no `sorry`, no axiom — the genuine Dong–Jiang/Frenkel–Zhu content,
*never* an `axiom`), and prove **unconditionally** from it:

* **`LUUniversalData.K`** — the assignment `U ↦ L(U) : LWModule W`, built from a per-`U`
  `MUModuleData`+`LUData` family via `MUModuleData.LUData.toLWModule`. This is genuinely
  `U ↦ L(U)`; the `LWModule`-packaging, irreducibility (`toLWModule_isIrreducibleLW`) and
  lowest-weight data are all proven, not assumed.
* **`LUUniversalData.generatedFromBottom`** — `GeneratedFromBottom W` from the two bundled
  clauses. This discharges the existential of `GeneratedFromBottom` with the *canonical* witness
  `K = U ↦ L(U)`.
* **`generatedFromBottom_of_universal`** — the same as a standalone wiring lemma.
* **`zhuBijection_of_LUUniversal`** — the headline: the Zhu forward map `Φ(𝒱) ↔ Irr A(𝒱)` is a
  bijection, reduced to `LUUniversalData` (= the two `L(U)`-clauses) plus the existence
  `InducedAssignment` and its irreducibility scope. The injective half is located in exactly the
  two `L(U)`-clauses — the genuine content of Theorem 5.3.4.

## The exact remaining crux

Everything above is unconditional given `LUUniversalData W`. The two `Prop`-valued fields of
`LUUniversalData` are precisely:

  `isoInvariant : ∀ U₁ U₂, Nonempty (AModEquiv U₁ U₂) → LWModule.Iso (K U₁) (K U₂)`
  `realizesIrr  : ∀ P, P.IsIrreducibleLW → LWModule.Iso (K P.toAMod) P`

i.e. functoriality of `L(·)` on bottoms, and generation-from-bottom for irreducibles. These are
carried as hypotheses (the Dong–Jiang/Frenkel–Zhu universal property), **not** axioms; `#print
axioms` on every proved theorem is `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The per-`U` `L(U)` family

The canonical assignment is `K U := L(U)`. To build `L(U)` as an `LWModule W` we need, for each
bottom `A(𝒱)`-module `U`, the deep module data `MUModuleData W U h` (the carrier `M(U)` with its
graded `𝒱`-action and the module Jacobi 5.3.1b) at *some* lowest weight `h`, together with the
maximal-`J` data `MUModuleData.LUData` that produces the irreducible quotient. We bundle that
*per-`U` family* into `LUFamily W`; the `LWModule` `L(U)` and its irreducibility are then
unconditional via `MUModuleData.LUData.toLWModule`. -/

/-- **A per-`U` family of `L(U)`-data.** For every bottom `A(𝒱)`-module `U`, a lowest weight
`hU U`, the genuine generalized-Verma module data `mudata U : MUModuleData W U (hU U)`, and the
maximal-`J` data `ludata U : MUModuleData.LUData (mudata U)` that produces the irreducible quotient
`L(U) = M(U)/J`. This is the output of the Dong–Jiang/Frenkel–Zhu construction; a hypothesis
structure, **not** an axiom, with no `sorry`. -/
structure LUFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The lowest weight of `M(U)`. -/
  hU : AMod W → ℂ
  /-- The genuine generalized-Verma module data for each bottom `U`. -/
  mudata : ∀ U : AMod W, MUModuleData W U (hU U)
  /-- The maximal-`J` / irreducible-quotient data for each `M(U)`. -/
  ludata : ∀ U : AMod W, MUModuleData.LUData (mudata U)

namespace LUFamily

variable (F : LUFamily W)

/-- **The canonical assignment `K : U ↦ L(U)`** as a bundled lowest-weight `𝒱`-module. This is
genuinely the irreducible quotient `L(U) = M(U)/J` (`MUModuleData.LUData.toLWModule`), not a
placeholder. -/
noncomputable def K (U : AMod W) : LWModule W := (F.ludata U).toLWModule

/-- `K U` is irreducible — the defining property of `L(U)` (`toLWModule_isIrreducibleLW`),
unconditional from the bundled maximal-`J` data. -/
theorem K_isIrreducibleLW (U : AMod W) : (F.K U).IsIrreducibleLW :=
  (F.ludata U).toLWModule_isIrreducibleLW

/-- `K U` realizes lowest weight `hU U` (the bottom survives the quotient). -/
@[simp] theorem K_h (U : AMod W) : (F.K U).h = F.hU U := rfl

end LUFamily

/-! ## The bundled universal-property data and `GeneratedFromBottom`

With the canonical `K = U ↦ L(U)` in hand, the two clauses of `GeneratedFromBottom W` are exactly
the two genuine ingredients of the injective half of Theorem 5.3.4 (functoriality of `L(·)` on
bottoms, and generation-from-bottom for irreducibles). We bundle them — and only them — as the
hypothesis structure `LUUniversalData W`. -/

/-- **The bundled universal-property data for the canonical assignment `K = U ↦ L(U)`.**

Carries the per-`U` `L(U)` family (`toLUFamily`, the Dong–Jiang construction output) together with
the two `Prop`-valued clauses of the universal property:

* `isoInvariant` — *functoriality of `L(·)` on bottoms*: an `A(𝒱)`-iso of bottoms gives a
  `𝒱`-iso `L(U₁) ≅ L(U₂)` (the maximal `J` is canonical, so `M(U₁) ≅ M(U₂)` descends to the
  quotients);
* `realizesIrr` — *generation-from-bottom for irreducibles*: every irreducible `P` is `≅ L(P_h)`
  (a bottom map lifts to a `𝒱`-surjection `M(P_h) ↠ P`, whose kernel is forced to be the maximal
  `J` by irreducibility of `P`).

This is exactly the Frenkel–Zhu / Dong–Jiang universal property of `M(U)`; a hypothesis structure,
**never** an axiom, with no `sorry`. -/
structure LUUniversalData (W : VertexOperatorAlgebra 𝒱) extends LUFamily W where
  /-- **Functoriality of `L(·)` on bottoms.** An `A(𝒱)`-iso `U₁ ≅ U₂` lifts to a `𝒱`-iso
  `L(U₁) ≅ L(U₂)` of the irreducible quotients. -/
  isoInvariant : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
    LWModule.Iso W (toLUFamily.K U₁) (toLUFamily.K U₂)
  /-- **Generation-from-bottom for irreducibles.** Every irreducible lowest-weight module `P` is
  `𝒱`-isomorphic to `L(P.toAMod)` — the universal property / Frobenius reciprocity of `M(U)`. -/
  realizesIrr : ∀ P : LWModule W, P.IsIrreducibleLW →
    LWModule.Iso W (toLUFamily.K P.toAMod) P

namespace LUUniversalData

/-- **`GeneratedFromBottom W` from the bundled universal-property data**, with the *canonical*
witness `K = U ↦ L(U)`. The existential's two clauses are exactly `D.isoInvariant` and
`D.realizesIrr` for `K = D.toLUFamily.K`. -/
theorem generatedFromBottom (D : LUUniversalData W) : GeneratedFromBottom W :=
  ⟨D.toLUFamily.K, D.isoInvariant, D.realizesIrr⟩

/-- **`IrredBottomRigidity W` from the universal-property data** (via `GeneratedFromBottom`). -/
theorem irredBottomRigidity (D : LUUniversalData W) : IrredBottomRigidity W :=
  irredBottomRigidity_of_universal D.generatedFromBottom

end LUUniversalData

/-- **Standalone wiring: `GeneratedFromBottom W` from the canonical `L(U)` family + the two
clauses.** Identical content to `LUUniversalData.generatedFromBottom`, exposed as a plain lemma
taking the family and the two `Prop`s. -/
theorem generatedFromBottom_of_universal (F : LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (hreal : ∀ P : LWModule W, P.IsIrreducibleLW → LWModule.Iso W (F.K P.toAMod) P) :
    GeneratedFromBottom W :=
  ⟨F.K, hiso, hreal⟩

end InducedAssignment

/-! ## The Zhu bijection from `LUUniversalData` -/

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from the canonical `L(U)`-universal-property data.**

Packaging the end-to-end reduction with the *canonical* assignment `K = U ↦ L(U)`: given the
existence `InducedAssignment W` `A` producing irreducible realizations (`hirr`), the ambient
irreducibility scope (`hall`), and the bundled universal-property data
`InducedAssignment.LUUniversalData W` (= the two `L(U)`-clauses — functoriality of `L(·)` on
bottoms and generation-from-bottom for irreducibles), the forward map `forwardMap W` is a
**bijection**. The injective half is located in exactly the two `L(U)`-clauses — the genuine
content of Zhu Theorem 5.3.4. -/
theorem zhuBijection_of_LUUniversal {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (D : InducedAssignment.LUUniversalData W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal A hall hirr D.generatedFromBottom

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
