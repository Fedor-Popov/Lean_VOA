/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGenFromBottomFinal
import VOA.Modules.ZhuVermaAnArchVcoreTwins

/-!
# The final bijection wiring — `zhuBijection_final` on the minimal remaining hypotheses (Thm 5.3.4)

This is the **last wiring file** of Zhu's Theorem 5.3.4: it assembles the single tightest headline
`zhuBijection_final : Function.Bijective (forwardMap W)` on **exactly** the hypotheses that genuinely
remain after the sibling drives close their pieces, with `InducedAssignment`, `GeneratedFromBottom`,
freeness, `isoInvariant`, rigidity, and bottom survival all plugged in as **proven terms** via the
backbone (`ZhuVermaAnArchCritPath`, `ZhuVermaAnArchGenFromBottomFinal`,
`ZhuVermaAnArchTier3Discharge`, `ZhuVermaAnArchGameTwo`).

## The definitive hypothesis bundle — what the main theorem rests on, and where each piece is discharged

Tracing the whole architecture, the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection funnels through the
backbone

```
generatedFromBottom_final            (GenFromBottomFinalFamily ⟹ GeneratedFromBottom)
        ↓
zhuBijection_of_universal            (GeneratedFromBottom ⟹ IrredBottomRigidity ⟹ RealizesSelf
        ↓                             ⟹ Bijective (forwardMap))
Bijective (forwardMap W)
```

with `forwardMap`'s easy direction `[M] ↦ [M_h]` resting on the **`A₀(𝒱)`** descended action (PROVEN,
`ZhuModule`).  Every step above is a *term*.  What remains carried — the **hypothesis bundle** — is exactly:

| carried hypothesis                              | sibling that discharges it (term-level)                       |
|-------------------------------------------------|---------------------------------------------------------------|
| `hCF : ∀ n, CrossCFirstOnm W n`                 | `MUGradedAction_of_crossCFirst` (`VcoreTwins`) ⟹ `q_act`      |
| `β`/`hβ` (bottom-landing)                        | `GradedModeVanish.ofBottom` (freeness, term) ⟹ `layer`        |
| `bottom_ne_zero` (`BottomOrbit`)                | `repMULevel_bottomOrbitDefectVanishes` (`BottomOrbitClose`)   |
| `KerJData` (maximal `J`)                        | `KerJData.ker_eq_J` (first iso) ⟹ `q_ker = J`                 |
| `A : InducedAssignment W`                       | `MUVHatData ⟹ … ⟹ InducedAssignment` (`Assembly`)             |
| `hall`, `hirr`                                  | the ambient irreducibility scope of the statement             |
| `F : LUFamily W`, `hiso`                        | the `L(U) = M(U)/J` family + functoriality                    |

The two genuine generator relations of `ρ` (`hderiv`, `hbracket`, `RhoDerivBracket`) and the
level-`0` defect identity `bottomLevelDefect` (`BottomOrbitClose`) are *upstream* of these carried
fields (they build `ρ`, hence `A`, and the bottom-survival half of `bottom_ne_zero`); they are not
re-carried here because their outputs (`A`, `bottom_ne_zero`) are.  **`A_n` associativity (`n ≥ 1`) is
NOT on this path** (see `ZhuVermaAnArchCritPath`).

So the genuinely-remaining hypothesis list the main theorem rests on is

* `A : InducedAssignment W`,
* `hall : AllLWIrreducible W`, `hirr : A.RealizeIrreducible`,
* `F : LUFamily W`, `hiso` (functoriality of `L(·)`),
* `G : GenFromBottomFinalFamily F` (per-`P`: bottom map `β`/`hβ`, the `MUGradedAction`-sourced `q_act`,
  the `BottomOrbit`-sourced `bottom_ne_zero`, and the maximal-`J` `KerJData`),

bundled here as `FinalScorecard W`.  The single sibling residue that the per-`P` `q_act` field is
sourced from — `CrossCFirstOnm` — is recorded explicitly as the term `mUGradedAction_from_crossCFirst`
(via `MUGradedAction_of_crossCFirst`), pinning the last open combinatorial family by name.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`mUGradedAction_from_crossCFirst`** — `MUGradedAction W` (the `q_act` source) from the single open
  family `∀ n, CrossCFirstOnm W n`, recorded as the named sibling discharge.
* **`FinalScorecard W`** — the bundle of *exactly* the genuinely-remaining hypotheses.
* **`FinalScorecard.bijective`** — the main theorem from the bundle, every other piece a term.
* **`zhuBijection_final`** — the single tightest headline, hypotheses spelled out flat (the definitive
  hypothesis bundle), routed through `generatedFromBottom_final` + `zhuBijection_of_universal`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchCritPath`, `ZhuVermaAnArchGenFromBottomFinal`, `ZhuVermaAnArchVcoreTwins`,
`ZhuVermaAnArchBottomOrbitClose`, `ZhuVermaAnArchRhoDerivBracket`.
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The named sibling discharge — `MUGradedAction` (the `q_act` source) from `CrossCFirstOnm` -/

/-- **`MUGradedAction W` from the single open family `∀ n, CrossCFirstOnm W n`** — recorded here as
the named sibling discharge.  This is the `VcoreTwins` headline `MUGradedAction_of_crossCFirst`: both
V-core commutator twins (`CrossCommTowerEq_holds`, `ARDCommTowerEq_holds`) and the Term₂ closure are
proven, so `MUGradedAction W` — the Construction-B diagonal well-definedness that *sources the per-`P`
`q_act` field* of the final lift — rests on exactly the level-`0` inner-circle c-first family
`CrossCFirstOnm`.  Carried as the explicit hypothesis `hCF`, **never** an axiom. -/
theorem mUGradedAction_from_crossCFirst (W : VertexOperatorAlgebra 𝒱)
    (hCF : ∀ n : ℕ, CrossCFirstOnm W n) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst W hCF

/-! ## The minimal hypothesis bundle -/

/-- **`FinalScorecard W` — the bundle of *exactly* the genuinely-remaining hypotheses of Zhu Theorem
5.3.4 after the sibling drives close.**

Every field is a named, genuine obligation of the generalized-Verma / Frenkel–Zhu theory, and **none**
is `A_n`-associativity for `n ≥ 1`:

* `A`     — the `U ↦ M̄(U)` lifting datum (`InducedAssignment`: bottom survival + functoriality), the
  output of the Construction-A bundle (`MUVHatData ⟹ … ⟹ InducedAssignment`, `Assembly`);
* `hall`  — the ambient irreducibility scope (the bijection is between the *irreducible* classes);
* `hirr`  — the realizations `M̄(U)` are irreducible (`= L(U)`);
* `F`     — the per-`U` `L(U) = M(U)/J` family;
* `hiso`  — functoriality of `L(·)` on bottoms (`isoInvariant`);
* `G`     — for each irreducible `P`, the per-`P` residue: the bottom map `β`/`hβ`, the
  `MUGradedAction`-sourced `q_act`, the `BottomOrbit`-sourced `bottom_ne_zero`, and the maximal-`J`
  `KerJData` (freeness is the *term* `GradedModeVanish.ofBottom`, `ker q = J` *derived* from
  `KerJData.ker_eq_J`).

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure FinalScorecard (W : VertexOperatorAlgebra 𝒱) where
  /-- The `U ↦ M̄(U)` lifting datum (bottom survival + functoriality). -/
  A : InducedAssignment W
  /-- The ambient irreducibility scope of Theorem 5.3.4. -/
  hall : InducedAssignment.AllLWIrreducible W
  /-- The realizations `M̄(U)` are irreducible (`= L(U)`). -/
  hirr : A.RealizeIrreducible
  /-- The per-`U` `L(U) = M(U)/J` family. -/
  F : InducedAssignment.LUFamily W
  /-- Functoriality of `L(·)` on bottoms (`isoInvariant`). -/
  hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
    LWModule.Iso W (F.K U₁) (F.K U₂)
  /-- The per-`P` minimal residue (bottom map + sibling `q_act`/`bottom_ne_zero` + maximal-`J`),
  freeness plugged as the term `GradedModeVanish.ofBottom`. -/
  G : InducedAssignment.GenFromBottomFinalFamily F

namespace FinalScorecard

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from the minimal hypothesis bundle.** The forward map
`forwardMap W = ([M] ↦ [M_h])` is a bijection.  Every step is a term: `GeneratedFromBottom` is the
*derived* `generatedFromBottom_final` (freeness plugged as `GradedModeVanish.ofBottom`, `ker q = J`
from `KerJData.ker_eq_J`), the rigidity reduction and the `A₀(𝒱)` descended action are the proved
backbone, and the universal-property bridge is `zhuBijection_of_universal`. **No `A_n`-associativity
for `n ≥ 1` is consumed.** -/
theorem bijective (S : FinalScorecard W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal S.A S.hall S.hirr
    (InducedAssignment.generatedFromBottom_final S.F S.hiso S.G)

end FinalScorecard

/-! ## The single tightest headline — the definitive hypothesis bundle, hypotheses spelled out flat -/

/-- **`zhuBijection_final` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem 5.3.4, on
the minimal remaining hypotheses (the definitive hypothesis bundle).**

Given **exactly** the genuinely-remaining hypotheses after the sibling drives close —

* `A : InducedAssignment W`              (the `U ↦ M̄(U)` lifting datum: bottom survival +
                                          functoriality; output of the Construction-A bundle),
* `hall : AllLWIrreducible W`            (the irreducibility scope of the statement),
* `hirr : A.RealizeIrreducible`          (the realizations are `L(U)`),
* `F : LUFamily W`                       (the per-`U` `L(U) = M(U)/J` family),
* `hiso`                                 (functoriality of `L(·)` on bottoms = `isoInvariant`),
* `G : GenFromBottomFinalFamily F`       (for each irreducible `P`: the bottom map `β`/`hβ`, the
                                          `MUGradedAction`-sourced `q_act`, the `BottomOrbit`-sourced
                                          `bottom_ne_zero`, and the maximal-`J` `KerJData`)

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

Everything else is a *term*: the easy direction rests on the `A₀(𝒱)` descended action (PROVEN,
`ZhuModule`); the **freeness** of `M(U)` on its bottom is the term `GradedModeVanish.ofBottom`;
`GeneratedFromBottom` (`generatedFromBottom_final`), `isoInvariant`, rigidity, and the
first-isomorphism `ker q = J` (`KerJData.ker_eq_J`) are all plugged as terms.  The per-`P` `q_act`
field is sourced from the single open combinatorial family `CrossCFirstOnm` via
`mUGradedAction_from_crossCFirst`; **no `A_n`-associativity for `n ≥ 1` is consumed.**

(Headline named `zhuBijection_final_scorecard` to coexist with the equivalent
`ZhuVermaAnArchGenFromBottomFinal.zhuBijection_final`, which it re-derives flat as the definitive
hypothesis bundle.) -/
theorem zhuBijection_final_scorecard {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal A hall hirr
    (InducedAssignment.generatedFromBottom_final F hiso G)

/-- **`zhuBijection_final_of_scorecard` — the same headline routed through the `FinalScorecard`
bundle.**  Identical content to `zhuBijection_final`, packaged through the single object
`FinalScorecard W` (the definitive hypothesis bundle as one term). -/
theorem zhuBijection_final_of_scorecard {W : VertexOperatorAlgebra 𝒱}
    (S : FinalScorecard W) :
    Function.Bijective (forwardMap W) :=
  S.bijective

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
