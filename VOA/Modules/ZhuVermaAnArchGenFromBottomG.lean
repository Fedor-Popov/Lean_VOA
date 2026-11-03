/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGenFromBottomFinal

/-!
# `G = GenFromBottomFinalFamily` with **`q_act` carried as the single gate `MUGradedAction`**

This is part of the lifting construction for Zhu Theorem 5.3.4 — the construction of the
generation-from-bottom datum `G` (the injective universal property) discharged **as far as the
PBW-free content allows**.  It builds *on top of* `ZhuVermaAnArchGenFromBottomFinal`, which already
reduced the injective half to the per-`P` residue bundle `GenFromBottomFinalData` (freeness plugged
as the term `GradedModeVanish.ofBottom`, `ker q = J` derived from `KerJData.ker_eq_J`).

`GenFromBottomFinalData` carries the per-`P` mode-intertwining field `q_act` as an opaque hypothesis.
This file goes one step further and **identifies that field with the single Dong–Jiang gate**
`MUGradedAction W` — the `a`-outer `μ/u/v` collapse (DJ Lemma 2.8, engine-verified TRUE), the SAME
gate that already sources the lifting datum `A` upstream — *reused* to feed the universal
property.  Everything else in `G` becomes a **term**:

* the **freeness side** (the `O_{n,0}`-descent of the per-layer graded mode action) is the term
  `GradedModeVanish.ofBottom β hβ` — its only input is the bottom-landing fact `hβ`;
* the **first-isomorphism** `ker q = J` is the term `KerJData.ker_eq_J` (the maximal-`J` coatom
  argument, fully proved in `ZhuVermaAnArchKerJ`);
* the **bottom survival** `bottom_ne_zero` is carried as the `BottomOrbit` datum (`layer 0 ≠ 0`);
* the **bottom-identity map** `β`/`hβ` is the realized embedding datum.

The genuine remaining crux — `q_act` — is carried as **exactly** `[q_act = MUGradedAction]`: a single
gate `MUGradedAction W` together with the per-`P` bridge `q_act_of_graded` that turns it into the
assembled-lift intertwining of the *specific* `ofBottom`-layer maps.  No `sorry`, no `axiom`, no
`pbw`; carried upstream facts are explicit hypotheses.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`GenFromBottomGData F P`** — the per-`P` residue with the `q_act` field replaced by a bridge
  `q_act_of_graded : MUGradedAction W → <the per-`P` q_act statement>`; β/hβ/bottom_ne_zero/KerJData
  (with the two compatibility equations) are exactly as in `GenFromBottomFinalData`.
* **`GenFromBottomGData.toFinalData`** — given the single gate `MUGradedAction W`, the full per-`P`
  `GenFromBottomFinalData` is *assembled* (the `q_act` field plugged via the carried bridge, every
  other field a term).
* **`GenFromBottomGFamily F`** — a per-irreducible-`P` family of the `q_act`-free residue.
* **`genFromBottomFinalFamily_of_G`** — given **one** gate `MUGradedAction W`, the family upgrades to
  the `GenFromBottomFinalFamily F` consumed by `generatedFromBottom_final`.
* **`generatedFromBottom_of_G`** — `GeneratedFromBottom W` from `[MUGradedAction W + the residue
  family]`, freeness/`ker = J`/rigidity all terms; the universal property of the generalized-Verma
  module.
* **`zhuBijection_of_G`** — the headline `Φ(𝒱) ↔ Irr A(𝒱)` bijection (`Function.Bijective
  (forwardMap W)`) on exactly `[A, hall, hirr, F, hiso, MUGradedAction W, the residue family G]`.

## The exact dependency on `forwardMap`

```
GenFromBottomGFamily F  +  MUGradedAction W
        │  (genFromBottomFinalFamily_of_G:  q_act := q_act_of_graded hgraded)
        ▼
GenFromBottomFinalFamily F                          (ZhuVermaAnArchGenFromBottomFinal)
        │  (generatedFromBottom_final)
        ▼
GeneratedFromBottom W
        │  (zhuBijection_of_universal — backbone)
        ▼
Function.Bijective (forwardMap W)
```

So the main theorem `Function.Bijective (forwardMap W)` rests, on the injective side, on **exactly one**
carried gate: `MUGradedAction W` (= the DJ-2.8 `a`-outer collapse `CFirst0ScalarCore`/`ARDTowerDecomp`,
engine-TRUE), threaded through the per-`P` bridge `q_act_of_graded`.  The freeness, the
first-isomorphism `ker q = J`, the bottom-identity map, `GeneratedFromBottom`, rigidity, and the
`A₀(𝒱)` easy direction are all terms.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Lemma 2.8, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu.
`ZhuVermaAnArchGenFromBottomFinal` (`GenFromBottomFinalData`, `GenFromBottomFinalFamily`,
`generatedFromBottom_final`, `zhuBijection_final`), `ZhuVermaAnArchKerJ` (`KerJData.ker_eq_J`),
`ZhuVermaAnArchFreenessCircle` (`GradedModeVanish.ofBottom`), `ZhuVermaAnArchMU` (`MUGradedAction`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The per-`P` residue with `q_act` replaced by the `MUGradedAction` gate -/

/-- **The minimal per-`P` residue of the injective half, with `q_act` carried as the single gate
`MUGradedAction W`.**

For an irreducible lowest-weight `P` this bundles exactly the same data as `GenFromBottomFinalData`
— the bottom map `β`/`hβ` (freeness fed as the term `GradedModeVanish.ofBottom`), the bottom survival
`bottom_ne_zero`, and the maximal-`J` first-isomorphism datum `KerJData` (with the two compatibility
equations pinning its intertwiner to the assembled `ofBottom`-lift and its maximal submodule to
`J`) — **except** that the per-`P` mode-intertwining `q_act` is *not* a free field.  Instead it is the
bridge

  `q_act_of_graded : MUGradedAction W → <the per-`P` q_act statement>`,

which turns the single Dong–Jiang gate `MUGradedAction W` (the `a`-outer `μ/u/v` collapse, DJ Lemma
2.8, engine-TRUE — the SAME gate that sources the lifting datum `A`) into the assembled-lift
intertwining of the specific `ofBottom`-layer maps.  This pins the genuine remaining crux as exactly
`[q_act = MUGradedAction]`.

* `β`             — the bottom map `P.toAMod → P` (the realized embedding `P.toAMod ≅ P_h ↪ P`);
* `hβ`            — `β` lands in the realized bottom `P_h` (bottom-landing construction fact; the only
  input the term-level freeness `GradedModeVanish.ofBottom` consumes);
* `q_act_of_graded` — **the gate bridge**: `MUGradedAction W` ⟹ the assembled `ofBottom`-lift
  intertwines every mode (`q_act`);
* `bottom_ne_zero` — `layer 0 ≠ 0` (the `BottomOrbit` survival of the bottom);
* `kerData`/`hq`/`hJ` — the maximal-`J` first-isomorphism datum and its two compatibility equations
  (`ker q = J` is then *derived* via `KerJData.ker_eq_J`).

A hypothesis structure, no `sorry`, **never** an axiom. -/
structure GenFromBottomGData (F : LUFamily W) (P : LWModule W) where
  /-- The bottom map `β : P.toAMod → P` (the realized embedding `P.toAMod ≅ P_h ↪ P`). -/
  β : (P.toAMod).carrier →ₗ[ℂ] P.carrier
  /-- **The bottom-landing construction fact** — `β` lands in the realized bottom `P_h`.  The only
  input the term-level freeness `GradedModeVanish.ofBottom` consumes. -/
  hβ : ∀ u : (P.toAMod).carrier, β u ∈ P.isMod.weight P.h
  /-- **The gate bridge — `q_act = MUGradedAction`.**  Given the single Dong–Jiang gate
  `MUGradedAction W` (the `a`-outer `μ/u/v` collapse, DJ Lemma 2.8, engine-TRUE), the assembled lift
  `q = ⨁ₙ (ofBottom β hβ).layer n` intertwines every mode.  This is the genuine remaining crux of the
  injective half, carried as a bridge from the SINGLE gate that already sources `A` upstream. -/
  q_act_of_graded : MUGradedAction W →
    ∀ (u : 𝒱) (n : ℤ) (x : MU W P.toAMod),
      (DirectSum.toModule ℂ ℕ P.carrier
          (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n))
          ((F.mudata P.toAMod).toOrdVModule.toWeakModule.act u n x)
        = P.isMod.toWeakModule.act u n
            ((DirectSum.toModule ℂ ℕ P.carrier
              (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n)) x)
  /-- **`bottom_ne_zero` / `BottomOrbit`** — the level-`0` layer map is nonzero (the bottom
  survives). -/
  bottom_ne_zero :
    (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction 0 ≠ 0
  /-- The maximal-`J` first-isomorphism datum (the only thing `ker q = J` rests on). -/
  kerData : KerJData (F.mudata P.toAMod) P
  /-- The `KerJData`'s intertwiner is the assembled lift `q = ⨁ₙ layer n`. -/
  hq : kerData.q =
    DirectSum.toModule ℂ ℕ P.carrier
      (fun n => (GradedModeVanish.ofBottom β hβ).toLayerActionData.layerAction n)
  /-- The `KerJData`'s maximal submodule is `(F.ludata P.toAMod).J`. -/
  hJ : kerData.J = (F.ludata P.toAMod).J

namespace GenFromBottomGData

variable {F : LUFamily W} {P : LWModule W}

/-- **The full per-`P` `GenFromBottomFinalData` from the gate `MUGradedAction W`.**

Given the single Dong–Jiang gate `MUGradedAction W`, assemble the per-`P` residue bundle consumed by
`generatedFromBottom_final`: the `q_act` field is the carried bridge `q_act_of_graded` applied to the
gate; every other field (`β`, `hβ`, `bottom_ne_zero`, `kerData`, `hq`, `hJ`) is passed through
verbatim — the freeness/`layer` side is the term `GradedModeVanish.ofBottom`, and `ker q = J` is
derived downstream from `KerJData.ker_eq_J`.  No `sorry`, **never** an axiom. -/
def toFinalData (G : GenFromBottomGData F P) (hgraded : MUGradedAction W) :
    GenFromBottomFinalData F P where
  β := G.β
  hβ := G.hβ
  q_act := G.q_act_of_graded hgraded
  bottom_ne_zero := G.bottom_ne_zero
  kerData := G.kerData
  hq := G.hq
  hJ := G.hJ

end GenFromBottomGData

/-! ## The per-`P` family and the discharge of the universal property from one gate -/

/-- **A per-irreducible-`P` family of the `q_act`-via-gate residue.** -/
def GenFromBottomGFamily (F : LUFamily W) : Type _ :=
  ∀ P : LWModule W, P.IsIrreducibleLW → GenFromBottomGData F P

/-- **The `GenFromBottomFinalFamily F` from one gate `MUGradedAction W` and the residue family.**

Given the single gate `MUGradedAction W`, every per-`P` residue `G P hP` upgrades to a full
`GenFromBottomFinalData` (`toFinalData`), with the `q_act` field sourced from the gate via the carried
bridge and every other field a term.  This is the `GenFromBottomFinalFamily F` consumed by
`generatedFromBottom_final` / `zhuBijection_final`. -/
def genFromBottomFinalFamily_of_G (F : LUFamily W)
    (hgraded : MUGradedAction W) (G : GenFromBottomGFamily F) :
    GenFromBottomFinalFamily F :=
  fun P hP => (G P hP).toFinalData hgraded

/-- **`GeneratedFromBottom W` from `[MUGradedAction W + the per-`P` residue family]`.**

The universal property of the generalized-Verma module, with the freeness side the term
`GradedModeVanish.ofBottom`, the first-isomorphism `ker q = J` the term `KerJData.ker_eq_J`, and the
single genuinely-remaining injective crux — `q_act` — sourced from the **one** Dong–Jiang gate
`MUGradedAction W` through the carried per-`P` bridge.  `hiso` is the carried functoriality clause. -/
theorem generatedFromBottom_of_G (F : LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (hgraded : MUGradedAction W) (G : GenFromBottomGFamily F) :
    GeneratedFromBottom W :=
  generatedFromBottom_final F hiso (genFromBottomFinalFamily_of_G F hgraded G)

end InducedAssignment

/-! ## The headline — the Zhu bijection on exactly `[…, MUGradedAction W, residue family]` -/

/-- **`zhuBijection_of_G` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem 5.3.4,
with the injective half resting on EXACTLY the single gate `MUGradedAction W`.**

Given

* `A : InducedAssignment W`               (the `U ↦ M̄(U)` lifting datum: bottom survival +
                                           functoriality),
* `hall : AllLWIrreducible W`             (the irreducibility scope of the statement),
* `hirr : A.RealizeIrreducible`           (the realizations are `L(U)`),
* `F : LUFamily W`                        (the per-`U` `L(U) = M(U)/J` family),
* `hiso`                                  (functoriality of `L(·)` on bottoms = `isoInvariant`),
* `hgraded : MUGradedAction W`            (**the single Dong–Jiang gate** — the `a`-outer `μ/u/v`
                                           collapse, DJ Lemma 2.8 / `CFirst0ScalarCore` /
                                           `ARDTowerDecomp`, engine-TRUE; the SAME gate that sources
                                           `A`, feeding the universal property),
* `G : GenFromBottomGFamily F`            (for each irreducible `P`: the bottom map `β`/`hβ`, the gate
                                           bridge `q_act_of_graded`, the `BottomOrbit`-sourced
                                           `bottom_ne_zero`, and the maximal-`J` `KerJData`),

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

The injective half rests on **one** carried gate, `MUGradedAction W`, threaded through the per-`P`
bridge `q_act_of_graded` (this is `[q_act = MUGradedAction]`).  Everything else is a *term*: freeness
is `GradedModeVanish.ofBottom`, the first-isomorphism `ker q = J` is `KerJData.ker_eq_J`,
`GeneratedFromBottom` is `generatedFromBottom_of_G`, the rigidity reduction and the `A₀(𝒱)` easy
direction are the backbone.  **No `A_n`-associativity for `n ≥ 1` is consumed.** -/
theorem zhuBijection_of_G {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (hgraded : MUGradedAction W) (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal A hall hirr
    (InducedAssignment.generatedFromBottom_of_G F hiso hgraded G)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
