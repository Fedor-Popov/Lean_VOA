/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHingeBridge
import VOA.Modules.ZhuVermaAnArchHingeCollapse
import VOA.Modules.ZhuVermaAnArchDJ28

/-!
# THE HINGE — the faithful Zhu bijection on the published Dong–Jiang Lemma 2.8

This is the main theorem of the rewiring.  It assembles, into a single named entry point, the
faithful (`hall`-free) Zhu Theorem 5.3.4 bijection `Φ(𝒱) ↔ Irr A(𝒱)`
(`zhuBijectionIrr_scorecard`, `ZhuVermaAnArchFaithfulBijection`) on top of **one** external mathematical
input — the published **Dong–Jiang Lemma 2.8** — carried here as the cross-instance hypothesis
`DJ28Cross W`.

Everything between `DJ28Cross` (+ the collapse `OnmFull = Onm`) and `Function.Bijective (forwardMapIrr W)`
is a **proven, axiom-clean term** assembled in the bridge / collapse / leaves files
(`ZhuVermaAnArchHingeBridge`, `-Collapse`, `-Leaves`).  No DJ feeder (Lemmas 2.2, 2.6, 2.7, 2.8) is
re-proved here.

## The chain, restated

```
DJ28Cross W                          -- published DJ Lemma 2.8 (cross instance, into OnmFull)
   │   [COLLAPSE  OnmFull W n 0 = Onm W n 0]
   ▼
anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0                 -- crossCirc0 membership
   │   [PROVEN MUGradedAction_of_crossCirc0, ZhuVermaAnArchHardMemCFirst2]
   ▼
MUGradedAction W                                                -- DJ M(U) graded-action crux
   │   [PROVEN genFromBottomFinalFamily_of_G, ZhuVermaAnArchGenFromBottomG]
   ▼
GenFromBottomFinalFamily F
   │   [PROVEN zhuBijectionIrr_scorecard, ZhuVermaAnArchFaithfulBijection — hall-free]
   ▼
Function.Bijective (forwardMapIrr W)
```

## What this file adds on top of the bridge

* **`phase4_of_dj28`** — the headline asked for: the faithful, `hall`-free bijection
  `Function.Bijective (forwardMapIrr W)` consuming the published DJ Lemma 2.8 cross-instance `hdj`
  together with the collapse `hcol` and the `hall`-free structural hypothesis bundle scope.  This is exactly
  `phase4_bijection_of_dj28` re-exported under the headline name with the dependency surface made
  explicit.
* **`phase4_of_dj28_solo`** — the SAME headline reduced to a single mathematical hypothesis by
  *folding the collapse into the published DJ-2.8 closure itself*: it consumes the full DJ Lemma 2.8
  closure-into-`OnmFull` (`DJ28IntoFull`, the genuine published conclusion the sibling DJ run lands)
  **plus** the collapse, and routes through `mUGradedAction_of_dj28_collapse`.
* **`phase4_of_dj28_neededSlice`** — the route that BYPASSES the full-blanket collapse: it consumes
  only the load-bearing `NeededSliceMems` (the three `M(U)` `𝒱`-action families directly into the
  partial ideal `Onm W n 0`), the minimal residual the faithful bijection actually needs.

## The DEFINITIVE open surface (honest)

After this file the faithful Zhu bijection rests on **DJ Lemma 2.8 plus the collapse
`OnmFull = Onm`**, where:

* **DJ Lemma 2.8** is `DJ28Cross W` (cross-instance, into `OnmFull`).  On disk the published lemma is
  `anmGen_OnmFull_right` / `anmGen_OnmFull_left` (`ZhuVermaAnArchDJ28`) **modulo** the residual
  structure `DJ28Residual` (the genuinely-open `O''`/`O'''` reassociation generator families; the two
  `O'` branches are closed there).  So the literal remaining content of DJ 2.8 is `DJ28Residual W n m p`
  — DJ's own remaining sub-steps after Lemma 2.7.  `DJ28Cross` is the cross-circle *instance* the
  `M(U)` action consumes; the sibling DJ run discharges it (the bridge carries it as the hypothesis,
  never re-proved here).
* the **collapse** `OnmFull W n 0 = Onm W n 0` is **NOT** a discharged term.  By
  `onmFull_eq_Onm_of_gens` (`ZhuVermaAnArchHingeCollapse`, FULLY proven reduction) it is equivalent to
  two into-`O'` generator memberships:
    * `assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0`     (DJ Lemma 2.6 into `O'`),
    * `levelMix W n 0 p a g v ∈ Onm W n 0`, `g ∈ Onm W p p` (DJ Lemma 2.7 into `O'`).
  The sibling `DJ26`/`DJ27` files land their published conclusions into `OnmFull` (`levelMixGen_mem_OnmFull`),
  or into `Onm` only modulo the open Borcherds residue `AssocBarExpand` (`assocBar_mem_Onm`).  Neither
  into-`Onm` family is an unconditional on-disk term.

So the bijection is NOT yet resting on DJ 2.8 *alone*: it rests on DJ 2.8 **and** the collapse.  The
collapse is engine-supported on the rank-1 free boson (`certificates/mathematica/hinge_rigor2.wl`,
basis-grade guarded) and is mathematically expected to hold for THIS ideal (the shifted-grading
absorption `anmRight_zero_Lgen_eq`, DJ Lemma 2.2, re-expresses the extra-summand generators as `O'`
circle generators — the DLM `V *_n O_0 ⊄ O_n` counterexample is for a *different*, unshifted ideal and
does not apply).  But it is correctly carried as a hypothesis, never faked.

**Fallback if the collapse cannot be discharged.**  Re-point the membership backbone
(`MUGradedAction_of_crossCirc0` / the `M(U)` quotient construction in `ZhuVermaAnArchMU`) from the
partial ideal `Onm W n 0` to the full ideal `OnmFull W n 0` — i.e. re-derive `MUGradedAction` against
`𝒱/OnmFull` instead of `𝒱/Onm`.  Then DJ 2.8 (`DJ28Cross`, into `OnmFull`) feeds it *directly*, no
collapse required, and the bijection rests on DJ Lemma 2.8 alone.  That re-point is a change to the
`MU` construction (`ZhuVermaAnArchMU`) and is not made here; it is the precise stated dependency,
documented not faked.

## References
Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826
(`math/0601626`), §2 (Lemmas 2.2, 2.6, 2.7, **2.8**), Thm 2.9; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The headline — the faithful Zhu bijection from DJ Lemma 2.8 + the collapse. -/

/-- **`phase4_of_dj28` — the faithful, `hall`-free Zhu Theorem 5.3.4 bijection `Φ(𝒱) ↔ Irr A(𝒱)`
resting on the published Dong–Jiang Lemma 2.8.**

Hypotheses:

* `hdj  : DJ28Cross W`   — the published DJ Lemma 2.8 cross-instance (full-ideal membership of the
  cross level-`0` circle `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ OnmFull W n 0`), carried, not proved;
* `hcol : CollapseHyp W` — the collapse `∀ n, OnmFull W n 0 = Onm W n 0` (see the file header — NOT a
  discharged term; engine-supported, carried as a hypothesis);

together with the `hall`-free structural hypothesis bundle scope `A`/`hirr`/`F`/`hiso`/`G` (every field a
proven term in the `Leaf*`/`R0`/`KerJ`/`GenFromBottomG` backbone).

Conclusion: the faithful forward map `forwardMapIrr W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, restricted to
*irreducible* iso-classes, is a **bijection**.

The injective half hinges on exactly the two carried inputs `hdj`, `hcol`; every combinatorial residue
downstream (`crossCirc0 → HARDmem → MUGradedAction`, the `q_act` bridge, freeness, `ker q = J`,
`GeneratedFromBottom`, the rigidity reduction, the `A₀(𝒱)` easy direction) is a proven term.  `hall` is
absent.  This is `phase4_bijection_of_dj28` (`ZhuVermaAnArchHingeBridge`) re-exported under the
headline name. -/
theorem phase4_of_dj28 {W : VertexOperatorAlgebra 𝒱}
    (hdj : DJ28Cross W) (hcol : CollapseHyp W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_bijection_of_dj28 hdj hcol A hirr F hiso G

/-! ## The same headline from the FULL published DJ-2.8 closure + the collapse.

`DJ28Cross` is the single cross-circle *instance* of DJ Lemma 2.8.  The sibling DJ run actually lands
the *full* closure `DJ28IntoFull` (the three `M(U)` `𝒱`-action families into `OnmFull`).  This variant
takes that full closure and the collapse, routing through `mUGradedAction_of_dj28_collapse`
(`ZhuVermaAnArchHingeCollapse`) so that the dependency surface is the genuine published DJ-2.8
conclusion, not just the single instance. -/

/-- **`phase4_of_dj28_full` — the faithful bijection from the full DJ-2.8 closure `DJ28IntoFull` + the
collapse `OnmCollapses`.**  `mUGradedAction_of_dj28_collapse` supplies `MUGradedAction W` from the
three families landing in `OnmFull` plus the per-level collapse; `genFromBottomFinalFamily_of_G` lifts
the residue family `G`; the `hall`-free `zhuBijectionIrr_scorecard` closes the bijection. -/
theorem phase4_of_dj28_full {W : VertexOperatorAlgebra 𝒱}
    (hDJ : DJ28IntoFull W) (hcol : ∀ n : ℕ, OnmCollapses W n)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijectionIrr_scorecard A hirr F hiso
    (InducedAssignment.genFromBottomFinalFamily_of_G F
      (mUGradedAction_of_dj28_collapse W hDJ hcol) G)

/-! ## The collapse-free route — only the load-bearing slice into the partial ideal. -/

/-- **`phase4_of_dj28_neededSlice` — the faithful bijection from the load-bearing slice alone,
bypassing the full-blanket collapse.**  Consumes only `NeededSliceMems W` (the three `M(U)`
`𝒱`-action families directly into the partial ideal `Onm W n 0` — the minimal residual the faithful
bijection actually needs, with the genuine load-bearing piece being the cross-circle `crossCirc`
family).  Routes through `mUGradedAction_of_neededSlice` (`ZhuVermaAnArchHingeCollapse`).  This is the
tightest dependency surface: it does not require `O''_{n,0} ⊆ O'_{n,0}` or `O'''_{n,0} ⊆ O'_{n,0}` for
*all* generators, only the `m = 0` slice the action consumes. -/
theorem phase4_of_dj28_neededSlice {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijectionIrr_scorecard A hirr F hiso
    (InducedAssignment.genFromBottomFinalFamily_of_G F
      (mUGradedAction_of_neededSlice W hslice) G)

/-! ## Status — the definitive open surface.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`admit`/`axiom`/`pbw`/`native_decide`):

* **`phase4_of_dj28`** — the headline: the faithful, `hall`-free `Function.Bijective (forwardMapIrr W)`
  from `[DJ28Cross + CollapseHyp + the hall-free hypothesis bundle scope]`.
* **`phase4_of_dj28_full`** — the same headline from the full published closure `DJ28IntoFull` plus the
  collapse `OnmCollapses`.
* **`phase4_of_dj28_neededSlice`** — the tightest route: the same headline from the load-bearing slice
  `NeededSliceMems` alone (no full-blanket collapse).

**The faithful Zhu bijection does NOT yet hinge on DJ Lemma 2.8 *alone*.**  It hinges on **DJ
Lemma 2.8 (`DJ28Cross`/`DJ28IntoFull`) PLUS the collapse `OnmFull W n 0 = Onm W n 0`** (or, in the
`neededSlice` route, the three `m = 0` `M(U)`-action families directly into `Onm`).  Precisely:

* DJ Lemma 2.8 itself is on disk as `anmGen_OnmFull_left`/`anmGen_OnmFull_right` (`ZhuVermaAnArchDJ28`),
  **modulo** the residual structure `DJ28Residual` (DJ's own open `O''`/`O'''` reassociation generator
  families and the DJ-2.5 sub-decomposition).  The cross-circle *instance* `DJ28Cross` is carried as
  the hypothesis the sibling DJ run discharges.
* the collapse is NOT a discharged term.  `onmFull_eq_Onm_of_gens` (FULLY proven) reduces it to two
  into-`O'` generator memberships — `assocDefect … ∈ Onm` (DJ 2.6) and `levelMix … ∈ Onm` (DJ 2.7).
  On disk DJ26 lands `assocBar_mem_Onm` into `Onm` only modulo the open Borcherds residue
  `AssocBarExpand`; DJ27 lands `levelMixGen_mem_OnmFull` into `OnmFull`.  Neither into-`Onm` family is
  an unconditional term yet.

So the DEFINITIVE open surface is the pair `[DJ28Cross, collapse]` — equivalently, after
`onmFull_eq_Onm_of_gens`, the two into-`O'` memberships above, with DJ 2.8's own residual
`DJ28Residual` underneath `DJ28Cross`.  The collapse is engine-supported (free boson, basis-grade
guarded) and expected to hold for THIS shifted-grading ideal; it is carried, never faked.

To reach DJ 2.8 *alone*, take the fallback in the header: re-point the `MU` quotient construction from
`Onm` to `OnmFull`, after which `DJ28Cross` (into `OnmFull`) feeds `MUGradedAction` directly.  That is
a change to `ZhuVermaAnArchMU` and is not made here. -/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.phase4_of_dj28
  #print axioms VOA.phase4_of_dj28_full
  #print axioms VOA.phase4_of_dj28_neededSlice
-/
