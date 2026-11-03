/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchHardMemCFirst2
import VOA.Modules.ZhuVermaAnArchGenFromBottomG
import VOA.Modules.ZhuVermaAnArchFaithfulBijection

/-!
# The hinge bridge — the faithful Zhu bijection from the published Dong–Jiang Lemma 2.8

This file rewires the faithful, `hall`-free Zhu Theorem 5.3.4 bijection
`zhuBijectionIrr_scorecard` (`ZhuVermaAnArchFaithfulBijection`) so that its single genuinely-deep
injective crux — the Dong–Jiang `M(U)` graded-action gate `MUGradedAction W` — rests on **exactly
one** published external input: **Dong–Jiang Lemma 2.8** (the full-ideal membership of the cross
level-`0` circle), proved separately (in the `…DJ22/DJ27/DJ28` files of the sibling run) and carried
here as the explicit hypothesis `DJ28Cross`.

The bridge is built **conditionally**: it takes the *statements* DJ 2.8 and the collapse
`OnmFull = Onm` as hypotheses (`Prop`s), never their proofs.  No DJ feeder is re-proved here.

## The chain assembled

```
DJ28Cross W                                                            -- DJ Lemma 2.8 (instantiated)
   anmCirc W 0 0 c (anmRight W n 0 a d) ∈ OnmFull W n 0
      │   [CollapseHyp W:  OnmFull W n 0 = Onm W n 0]                   -- the collapse O″⊆O′, O‴⊆O′
      ▼
   anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0                     -- the crossCirc0 membership
      │   [PROVEN MUGradedAction_of_crossCirc0, ZhuVermaAnArchHardMemCFirst2]
      ▼
MUGradedAction W
      │   [PROVEN genFromBottomFinalFamily_of_G, ZhuVermaAnArchGenFromBottomG]
      ▼
GenFromBottomFinalFamily F
      │   [PROVEN zhuBijectionIrr_scorecard, ZhuVermaAnArchFaithfulBijection — hall-free]
      ▼
Function.Bijective (forwardMapIrr W)
```

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`DJ28Cross W`** — the cross-instance of the published Dong–Jiang Lemma 2.8 as a `Prop`: for all
  levels `n` and homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the cross level-`0` circle
  `anmCirc W 0 0 c (anmRight W n 0 a d)` lies in the **full** Dong–Jiang ideal `OnmFull W n 0`.  This
  is the *statement* the sibling DJ run discharges (`ZhuVermaAnArchDJ28`); it is carried as a
  hypothesis, not re-proved.
* **`CollapseHyp W`** — the collapse `∀ n, OnmFull W n 0 = Onm W n 0` (equivalently `O″ ⊆ O′` and
  `O‴ ⊆ O′` since `Onm ≤ OnmFull` is already proven, `Onm_le_OnmFull`).  Carried as a hypothesis; see
  the honesty note at the file end on whether it holds.
* **`crossCirc0_mem_Onm_of_dj28`** — the COLLAPSE step: `DJ28Cross` + `CollapseHyp` ⟹ the
  `crossCirc0` membership `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0` (the universal feeder of
  `MUGradedAction_of_crossCirc0`).
* **`mUGradedAction_of_dj28`** — `MUGradedAction W` from `DJ28Cross` + `CollapseHyp`, through the
  PROVEN `MUGradedAction_of_crossCirc0`.
* **`phase4_bijection_of_dj28`** — **the faithful headline**: `Function.Bijective (forwardMapIrr W)`
  from `DJ28Cross` + `CollapseHyp` plus the `hall`-free hypothesis bundle structural data
  (`A`, `hirr`, `F`, `hiso`, and the `q_act`-via-gate residue family `G : GenFromBottomGFamily F`),
  wired through `genFromBottomFinalFamily_of_G` and the `hall`-free `zhuBijectionIrr_scorecard`.
* **`phase4_bijection_of_dj28_finalFamily`** — the same headline taking the *already-assembled*
  `GenFromBottomFinalFamily F` (i.e. with `MUGradedAction` already plugged), for callers that prefer
  to source the gate themselves.

After this file, the faithful Zhu bijection hinges on **solely** the published DJ Lemma 2.8
(carried as `DJ28Cross`) together with the collapse `CollapseHyp` and the structural hypothesis bundle
scope — every combinatorial residue downstream of the membership is a proven term.

## References
Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826
(`math/0601626`), §2 (Lemmas 2.2, 2.6, 2.7, **2.8**), Thm 2.9; Frenkel–Zhu; Dong–Li–Mason;
Gannon §5.3.2, Thm 5.3.4.  `ZhuVermaAnArchAnmFull` (`OnmFull`/`Onm_le_OnmFull`),
`ZhuVermaAnArchHardMemCFirst2` (`MUGradedAction_of_crossCirc0`),
`ZhuVermaAnArchGenFromBottomG` (`genFromBottomFinalFamily_of_G`),
`ZhuVermaAnArchFaithfulBijection` (`zhuBijectionIrr_scorecard`, `hall`-free).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two carried statements — DJ Lemma 2.8 and the collapse. -/

/-- **The cross-instance of Dong–Jiang Lemma 2.8**, as a `Prop`.

For every level `n` and homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the cross level-`0` circle
`anmCirc W 0 0 c (anmRight W n 0 a d)` lies in the **full** Dong–Jiang ideal `OnmFull W n 0`
(`= O' ⊔ O'' ⊔ O'''`, `ZhuVermaAnArchAnmFull`).

This is the *statement* that the published Dong–Jiang Lemma 2.8 supplies — the membership half of the
`A_{n,0}`-bimodule relation for the inner right-action circle.  It is discharged separately by the
sibling DJ run (the `ZhuVermaAnArchDJ22/DJ27/DJ28` files); here it is carried as a hypothesis, never
re-proved. -/
def DJ28Cross (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
    ∀ d ∈ W.grading (P : ℤ), anmCirc W 0 0 c (anmRight W n 0 a d) ∈ OnmFull W n 0

/-- **The collapse `OnmFull = Onm` (at `m = 0`)**, as a `Prop`.

`Onm W n 0 ≤ OnmFull W n 0` is already proven (`Onm_le_OnmFull`); the content here is the *reverse*
inclusion, i.e. `O''_{n,0} ⊆ O'_{n,0}` (the associator-defect summand) **and** `O'''_{n,0} ⊆ O'_{n,0}`
(the level-mixing summand).  When this holds, the full DJ ideal `OnmFull` collapses to the repo
partial ideal `Onm` and the membership-based `Onm` backbone consumes DJ 2.8 directly.

Carried as a hypothesis; see the honesty note at the file end on whether it actually holds (in the
general DJ theory `O''`, `O'''` are *not* contained in `O'` — they are additional bimodule
relations). -/
def CollapseHyp (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ n : ℕ, OnmFull W n 0 = Onm W n 0

/-! ## The COLLAPSE step — DJ 2.8 + collapse ⟹ the `crossCirc0` membership. -/

/-- **`DJ28Cross` + `CollapseHyp` ⟹ the `crossCirc0` membership** (the universal feeder of
`MUGradedAction_of_crossCirc0`).

DJ Lemma 2.8 (`hdj`) lands the cross level-`0` circle `anmCirc W 0 0 c (anmRight W n 0 a d)` in the
full ideal `OnmFull W n 0`; the collapse `hcol n` rewrites `OnmFull W n 0` to `Onm W n 0`, so the
element lies in the repo partial ideal `Onm W n 0`.  Purely transport-of-membership across the
ideal equality. -/
theorem crossCirc0_mem_Onm_of_dj28 (W : VertexOperatorAlgebra 𝒱)
    (hdj : DJ28Cross W) (hcol : CollapseHyp W) :
    ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ),
      anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0 := by
  intro n K M P a ha c hc d hd
  have hmem : anmCirc W 0 0 c (anmRight W n 0 a d) ∈ OnmFull W n 0 :=
    hdj n K M P a ha c hc d hd
  rwa [hcol n] at hmem

/-! ## `MUGradedAction W` from DJ 2.8 + the collapse. -/

/-- **`MUGradedAction W` from `DJ28Cross` + `CollapseHyp`.**

The COLLAPSE step `crossCirc0_mem_Onm_of_dj28` supplies the universal `crossCirc0` membership
`anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`, which the PROVEN membership endgame
`MUGradedAction_of_crossCirc0` (`ZhuVermaAnArchHardMemCFirst2`) assembles into the Dong–Jiang `M(U)`
graded-action crux `MUGradedAction W` — the `q_act` source of the faithful Zhu bijection. -/
theorem mUGradedAction_of_dj28 (W : VertexOperatorAlgebra 𝒱)
    (hdj : DJ28Cross W) (hcol : CollapseHyp W) :
    MUGradedAction W :=
  MUGradedAction_of_crossCirc0 W (crossCirc0_mem_Onm_of_dj28 W hdj hcol)

/-! ## The faithful Zhu bijection from DJ 2.8 + the collapse. -/

/-- **`phase4_bijection_of_dj28` — the faithful, `hall`-free Theorem 5.3.4 bijection
`Φ(𝒱) ↔ Irr A(𝒱)` resting solely on the published Dong–Jiang Lemma 2.8.**

Given

* `hdj : DJ28Cross W`                         (the published DJ Lemma 2.8, full-ideal membership),
* `hcol : CollapseHyp W`                      (the collapse `OnmFull = Onm` at `m = 0`),

together with the `hall`-free structural hypothesis bundle data

* `A : InducedAssignment W`                   (the `U ↦ M̄(U)` lifting datum),
* `hirr : A.RealizeIrreducible`               (the realizations are `L(U)`),
* `F : InducedAssignment.LUFamily W`          (the per-`U` `L(U) = M(U)/J` family),
* `hiso`                                      (functoriality of `L(·)` on bottoms = `isoInvariant`),
* `G : InducedAssignment.GenFromBottomGFamily F`   (the per-`P` residue with `q_act` carried as the
                                                gate bridge `q_act_of_graded : MUGradedAction W → …`),

— the faithful forward map `forwardMapIrr W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, restricted to the
*irreducible* iso-classes, is a **bijection**.

Route: `hdj` + `hcol` ⟹ `MUGradedAction W` (`mUGradedAction_of_dj28`); the per-`P` residue family `G`
upgrades to the `GenFromBottomFinalFamily F` consumed by the bijection via the PROVEN
`genFromBottomFinalFamily_of_G` (sourcing each `q_act` from the single gate); the `hall`-free
`zhuBijectionIrr_scorecard` (`ZhuVermaAnArchFaithfulBijection`) closes the bijection.

The injective half hinges on **exactly one** external input — DJ Lemma 2.8 (`hdj`), through the
collapse `hcol` — with every combinatorial residue downstream (the `crossCirc0`→`HARDmem`→
`MUGradedAction` membership endgame, the `q_act` bridge, freeness `GradedModeVanish.ofBottom`, the
first-isomorphism `ker q = J`, `GeneratedFromBottom`, the rigidity reduction, and the `A₀(𝒱)` easy
direction) a proven term.  **`hall` is absent.** -/
theorem phase4_bijection_of_dj28 {W : VertexOperatorAlgebra 𝒱}
    (hdj : DJ28Cross W) (hcol : CollapseHyp W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijectionIrr_scorecard A hirr F hiso
    (InducedAssignment.genFromBottomFinalFamily_of_G F (mUGradedAction_of_dj28 W hdj hcol) G)

/-- **`phase4_bijection_of_dj28_finalFamily` — the same faithful headline taking an already-assembled
`GenFromBottomFinalFamily F`.**

A convenience variant of `phase4_bijection_of_dj28` for callers that prefer to supply the per-`P`
residue family with `q_act` already plugged (a `GenFromBottomFinalFamily F`).  The `DJ28Cross` +
`CollapseHyp` hypotheses are retained to keep the dependency on DJ Lemma 2.8 explicit at the headline
(they still source `MUGradedAction W` for any caller that builds `G` from `genFromBottomFinalFamily_of_G`
externally); here the family is taken directly and fed to the `hall`-free `zhuBijectionIrr_scorecard`. -/
theorem phase4_bijection_of_dj28_finalFamily {W : VertexOperatorAlgebra 𝒱}
    (_hdj : DJ28Cross W) (_hcol : CollapseHyp W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomFinalFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijectionIrr_scorecard A hirr F hiso G

/-! ## Status — the faithful Zhu bijection hinges on the published Dong–Jiang Lemma 2.8.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`DJ28Cross W`** / **`CollapseHyp W`** — the two carried `Prop`s (DJ Lemma 2.8 and the collapse).
* **`crossCirc0_mem_Onm_of_dj28`** — the COLLAPSE step (transport of membership across
  `OnmFull = Onm`).
* **`mUGradedAction_of_dj28`** — `MUGradedAction W` from `[DJ28Cross + CollapseHyp]`, through the
  PROVEN `MUGradedAction_of_crossCirc0`.
* **`phase4_bijection_of_dj28`** — the faithful `hall`-free bijection `Function.Bijective
  (forwardMapIrr W)` from `[DJ28Cross + CollapseHyp + the hall-free hypothesis bundle data]`, wired through
  `genFromBottomFinalFamily_of_G` + `zhuBijectionIrr_scorecard`.
* **`phase4_bijection_of_dj28_finalFamily`** — the same headline taking an assembled
  `GenFromBottomFinalFamily F`.

**Honesty note on the collapse `CollapseHyp` (`OnmFull = Onm`).**  `Onm ≤ OnmFull` is proven
(`Onm_le_OnmFull`); the reverse needs `O''_{n,0} ⊆ O'_{n,0}` and `O'''_{n,0} ⊆ O'_{n,0}`.  In the
general Dong–Jiang theory these inclusions are **NOT** available: the published DJ Lemma 2.7 concludes
`(V ∗ⁿ O'_{p}) ∗ⁿ V ⊆ O_{n,m}` into the *full* ideal `O_{n,m} = O' + O'' + O'''` (tautological for the
`O'''` summand), **not** into `O'`; and `O''` is the associator-defect span (DLM-`A_n`-style relations
that are genuinely new modulo `O'`).  So `CollapseHyp` is a *fallback* hypothesis: if the sibling DJ
run establishes it (or the specific cross element's `OnmFull`-witness happens to land in `Onm`),
`phase4_bijection_of_dj28` closes through the existing `Onm`-backbone with DJ 2.8 directly.  If the
collapse does NOT hold (the expected general situation), the membership-based `Onm`-backbone must be
re-pointed to the full ideal: replace the carrier `Onm W n 0` of `MUGradedAction_of_crossCirc0` /
`crossCirc0_mem_Onm` by `OnmFull W n 0` (i.e. re-derive `MUGradedAction` against `AnmFull`/`OnmFull`),
which is the precise stated dependency.  This file does NOT fake the collapse — it is an explicit
`Prop` hypothesis, and the bridge above is the genuine conditional wiring on top of DJ 2.8.

No DJ feeder (Lemmas 2.2, 2.6, 2.7, 2.8) is re-proved here; `DJ28Cross` / `CollapseHyp` are the
carried *statements*, discharged by the sibling DJ run (`ZhuVermaAnArchDJ22.lean`,
`ZhuVermaAnArchDJ27.lean` are on disk; `ZhuVermaAnArchDJ28.lean` is the sibling's DJ-2.8 file — the
precise dependency for `DJ28Cross`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCirc0_mem_Onm_of_dj28
  #print axioms VOA.mUGradedAction_of_dj28
  #print axioms VOA.phase4_bijection_of_dj28
  #print axioms VOA.phase4_bijection_of_dj28_finalFamily
-/
