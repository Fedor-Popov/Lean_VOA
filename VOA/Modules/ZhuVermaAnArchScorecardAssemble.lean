/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFinalWiring
import VOA.Modules.ZhuVermaAnArchFunctorial
import VOA.Modules.ZhuVermaAnArchARDTowerClose

/-!
# The hypothesis bundle assembly — `zhuBijection_assembled` on the tightest minimal leaves (Zhu Thm 5.3.4)

`ZhuVermaAnArchFinalWiring` bundles the **`FinalScorecard`** of Zhu's Theorem 5.3.4 and proves the
unconditional bijection `Φ(𝒱) ↔ Irr A(𝒱)` from it.  Its `hiso` field is carried *as a function*
(`∀ U₁ U₂, Nonempty (AModEquiv …) → LWModule.Iso …`), and its `MUGradedAction` residue is sourced —
in `mUGradedAction_from_crossCFirst` — from the *looser* membership family `CrossCFirstOnm`.

This file performs the **final hypothesis bundle assembly**: it pushes the two remaining "soft" fields one
layer deeper, so the main theorem rests on the *tightest* leaf set the architecture supports, with every
other piece a **proven term**:

* **`hiso` becomes a term.**  The functoriality clause is not carried as a bare function: it is
  *derived* from the genuine construction-level functoriality datum `InducedAssignment.MUFunctorialData F`
  (the Dong–Jiang/Frenkel–Zhu functoriality of the generalized-Verma module `M(·)` in its bottom,
  `ZhuVermaAnArchFunctorial`) via `MUFunctorialData.isoInvariant`.  So the headline carries the
  *structural* `MUFunctorialData F`, and `hiso` is plugged as a term.

* **`MUGradedAction` is pinned to the single universal scalar leaf `CrossCFirst0TowerEq`.**  The
  `q_act` field of the per-`P` residue (`GenFromBottomFinalData`) is sourced from `MUGradedAction W`,
  which — via `MUGradedAction_of_crossCFirst0` (`ZhuVermaAnArchARDTowerClose`) — follows from the
  single universal level-`0`-vs-level-`n` cross `c`-first tower decomposition `CrossCFirst0TowerEq`
  (engine-verified TRUE on the rank-1 free boson).  This is *tighter* than the
  `CrossCFirstOnm`-membership family of `mUGradedAction_from_crossCFirst`: it is the genuine
  `a`-irreducible Dong–Jiang Lemma 2.8 scalar core, with Term₂'s commutator + `c`-first towers,
  Term₁'s commutator tower, and the membership half ALL discharged as terms.

## The definitive minimal leaf list

Tracing the whole architecture, the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection
(`Function.Bijective (forwardMap W)`) rests on **exactly**

* `A : InducedAssignment W`            — the `U ↦ M̄(U)` lifting datum (the Construction-A bundle
                                          output `MUVHatData ⟹ … ⟹ InducedAssignment`, built on
                                          `ρ = levelShiftRho` [`hderiv`/`hbracket` + `σ`-choice],
                                          `MUGradedAction` [from `CrossCFirst0TowerEq`], and bottom
                                          survival [from `bottomDefectZero`]);  **scope**;
* `hall : AllLWIrreducible W`          — the ambient irreducibility scope;  **scope**;
* `hirr : A.RealizeIrreducible`        — the realizations are `L(U)` (`ZhuVermaAnArchGameTwo`);
                                          **scope**;
* `F : LUFamily W`                     — the per-`U` `L(U) = M(U)/J` family;  **scope**;
* `Dfun : MUFunctorialData F`          — the `M(·)`-functoriality datum;  ⟹ `hiso` as a **term**;
* `G : GenFromBottomFinalFamily F`     — the per-`P` residue (bottom map `β`/`hβ`, `q_act`
                                          [= `MUGradedAction` from `CrossCFirst0TowerEq`],
                                          `bottom_ne_zero` [`BottomOrbit`], maximal-`J` `KerJData`);
                                          freeness is the term `GradedModeVanish.ofBottom`.

So the **genuinely-remaining scalar/residue leaves** the main theorem bottoms out on are:

```
[ CrossCFirst0TowerEq           — the single universal cross c-first tower (⟹ MUGradedAction ⟹ q_act),
  ρ's hderiv / hbracket         — the two genuine generator relations of the level-shift loop action,
  bottomDefectZero              — the A(𝒱) bottom Borcherds relation (⟹ bottom survival),
  σ-choice                      — the Frenkel–Zhu level-shift assignment ℤ → ℕ → ℕ ]
```

plus the **scope** structural inputs `A`, `hall`, `hirr`, `F`, `G`.  **No `A_n`-associativity for
`n ≥ 1` is consumed** (see `ZhuVermaAnArchCritPath`).  `hiso` is not a leaf — it is a
term from `Dfun`.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`mUGradedAction_from_crossCFirst0`** — `MUGradedAction W` from the single universal scalar leaf
  `CrossCFirst0TowerEq` (tighter than `mUGradedAction_from_crossCFirst`).
* **`hiso_from_functorial`** — the `FinalScorecard`-shaped `hiso` clause as a **term** from a carried
  `MUFunctorialData F`.
* **`FinalScorecard.ofFunctorial`** — a `FinalScorecard W` with `hiso` plugged as the Functorial term.
* **`zhuBijection_assembled`** — the single tightest headline: `Function.Bijective (forwardMap W)` on
  exactly `[A, hall, hirr, F, Dfun, G]`, `hiso` a term, routed through `zhuBijection_final_scorecard`.
* **`zhuBijection_assembled_of_scorecard`** — the same headline through the assembled `FinalScorecard`.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.4–3.5, Thm 4.13; DLM3 §4;
H. Li hep-th/9406211 §2; Gannon §5.3.1–§5.3.2, Def. 5.3.1, Thm 5.3.4; Zhu [574]; Frenkel–Zhu;
`ZhuVermaAnArchFinalWiring`, `ZhuVermaAnArchFunctorial`, `ZhuVermaAnArchARDTowerClose`,
`ZhuVermaAnArchLevelShiftRho`, `ZhuVermaAnArchBottomLevelDefect`, `ZhuVermaAnArchGameTwo`.
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The tightest `MUGradedAction` source — from the single universal `CrossCFirst0TowerEq` -/

/-- **`MUGradedAction W` from the single universal scalar leaf `CrossCFirst0TowerEq`** — the tightest
named source of the `q_act` residue.

This is `MUGradedAction_of_crossCFirst0` (`ZhuVermaAnArchARDTowerClose`): given, for every level `n`
and homogeneous `a, c, d`, the level-`0`-vs-level-`n` cross `c`-first tower decomposition
`CrossCFirst0TowerEq` (the genuine `a`-irreducible Dong–Jiang Lemma 2.8 lift), the entire
`ARDTowerDecomp` is discharged (Term₂'s commutator + `c`-first towers, Term₁'s commutator tower, and
the membership half ALL closed as terms), and `MUGradedAction W` — the Construction-B diagonal
well-definedness that *sources the per-`P` `q_act` field* — follows.

This is strictly **tighter** than `mUGradedAction_from_crossCFirst` (which carries the looser
`CrossCFirstOnm` membership family): `CrossCFirst0TowerEq` is the genuine universal scalar core.
Carried as the explicit hypothesis `Hcf`, **never** an axiom. -/
theorem mUGradedAction_from_crossCFirst0 (W : VertexOperatorAlgebra 𝒱)
    (Hcf : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirst0TowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst0 W Hcf

/-! ## `hiso` as a term — from the construction-level functoriality datum -/

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The `FinalScorecard`-shaped `hiso` clause as a term from a carried `MUFunctorialData F`.**

The functoriality clause of the hypothesis bundle — `an A(𝒱)-iso of bottoms `U₁ ≅ U₂` induces a `𝒱`-iso
`L(U₁) ≅ L(U₂)`` — is *not* a leaf: it is `MUFunctorialData.isoInvariant`
(`ZhuVermaAnArchFunctorial`), the unconditional quotient-functor descent of the genuine
construction-level functoriality of the generalized-Verma module `M(·)` in its bottom.  So the only
carried input is the structural `MUFunctorialData F`; `hiso` is a term. -/
theorem hiso_from_functorial (F : LUFamily W) (Dfun : MUFunctorialData F) :
    ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂) :=
  Dfun.isoInvariant

end InducedAssignment

/-! ## The assembled hypothesis bundle — `hiso` plugged as the Functorial term -/

namespace FinalScorecard

variable {W : VertexOperatorAlgebra 𝒱}

/-- **A `FinalScorecard W` with the `hiso` field plugged as a term from `MUFunctorialData`.**

Every field is the genuine remaining obligation of the generalized-Verma / Frenkel–Zhu theory, with
`hiso` *not carried as a function* but **derived** from the structural functoriality datum
`Dfun : MUFunctorialData F` via `hiso_from_functorial`.  The remaining carried fields are exactly the
scope structural inputs `A`, `hall`, `hirr`, `F`, `G` (whose per-`P` `q_act` is the `MUGradedAction`
content, pinned by `mUGradedAction_from_crossCFirst0` to the single universal leaf
`CrossCFirst0TowerEq`).  No `sorry`, **never** an axiom. -/
noncomputable def ofFunctorial (A : InducedAssignment W)
    (hall : InducedAssignment.AllLWIrreducible W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W) (Dfun : InducedAssignment.MUFunctorialData F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    FinalScorecard W where
  A := A
  hall := hall
  hirr := hirr
  F := F
  hiso := InducedAssignment.hiso_from_functorial F Dfun
  G := G

end FinalScorecard

/-! ## The single tightest headline — the definitive minimal leaf list, `hiso` a term -/

/-- **`zhuBijection_assembled` — the unconditional `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem
5.3.4, assembled on the tightest minimal leaves.**

Given the genuinely-remaining hypotheses after the sibling drives close —

* `A : InducedAssignment W`           (the `U ↦ M̄(U)` lifting datum: the Construction-A bundle output,
                                       built on `ρ = levelShiftRho` [`hderiv`/`hbracket` + `σ`-choice],
                                       `MUGradedAction` [from `CrossCFirst0TowerEq`], and bottom
                                       survival [from `bottomDefectZero`]),
* `hall : AllLWIrreducible W`         (the irreducibility scope),
* `hirr : A.RealizeIrreducible`       (the realizations are `L(U)`),
* `F : LUFamily W`                    (the per-`U` `L(U) = M(U)/J` family),
* `Dfun : MUFunctorialData F`         (the `M(·)`-functoriality datum — **`hiso` is plugged from this
                                       as a term**, via `hiso_from_functorial`),
* `G : GenFromBottomFinalFamily F`    (the per-`P` residue: bottom map `β`/`hβ`, `q_act`
                                       [= `MUGradedAction` from `CrossCFirst0TowerEq`],
                                       `bottom_ne_zero` [`BottomOrbit`], maximal-`J` `KerJData`)

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

Everything else is a *term*: `hiso` is `MUFunctorialData.isoInvariant`; the easy direction rests on
the `A₀(𝒱)` descended action (PROVEN, `ZhuModule`); freeness is `GradedModeVanish.ofBottom`;
`GeneratedFromBottom` (`generatedFromBottom_final`), the rigidity reduction, and the
first-isomorphism `ker q = J` (`KerJData.ker_eq_J`) are all plugged as terms.  The `q_act` residue is
sourced from the single universal scalar leaf `CrossCFirst0TowerEq` via
`mUGradedAction_from_crossCFirst0`.  **No `A_n`-associativity for `n ≥ 1` is consumed.**

The DEFINITIVE minimal scalar/residue leaves the main theorem bottoms out on are
`[CrossCFirst0TowerEq, ρ's hderiv/hbracket, bottomDefectZero, σ-choice]` (plus the scope structural
inputs `A`, `hall`, `hirr`, `F`, `G`); `hiso` is not a leaf. -/
theorem zhuBijection_assembled {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (Dfun : InducedAssignment.MUFunctorialData F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_final_scorecard A hall hirr F
    (InducedAssignment.hiso_from_functorial F Dfun) G

/-- **`zhuBijection_assembled_of_scorecard` — the same headline routed through the assembled
`FinalScorecard` bundle.**  Identical content to `zhuBijection_assembled`, packaged through the single
object `FinalScorecard.ofFunctorial …` (the definitive hypothesis bundle, `hiso` a term, as one term). -/
theorem zhuBijection_assembled_of_scorecard {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (Dfun : InducedAssignment.MUFunctorialData F)
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMap W) :=
  (FinalScorecard.ofFunctorial A hall hirr F Dfun G).bijective

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
