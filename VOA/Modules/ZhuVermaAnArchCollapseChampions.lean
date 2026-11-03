/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCollapseAssoc
import VOA.Modules.ZhuVermaAnArchCollapseLevel
import VOA.Modules.ZhuVermaAnArchUpCrossClosure
import VOA.Modules.ZhuVermaAnArchUpRightModule
import VOA.Modules.ZhuVermaAnArchFaithfulBijection

/-!
# The COLLAPSE ENDGAME — the maximal assembled fragment, and the EXACT remaining residual

The faithful Zhu bijection `Function.Bijective (forwardMapIrr W)`
(`ZhuVermaAnArchFaithfulBijection`, Gannon Thm 5.3.4) consumes the Dong–Jiang `M(U)` graded-action
crux `MUGradedAction W` (`ZhuVermaAnArchMU`) as the substrate of the per-`P` `q_act` field of the
universal-property hypothesis bundle `G : GenFromBottomFinalFamily`.  The hinge analysis
(`ZhuVermaAnArchHingeCollapse`, `-UpCrossClosure`, `-UpRightModule`) reduced the *entire*
`MUGradedAction` crux to the single collapse predicate, at every level,

  `OnmCollapses W n  :=  OnmFull W n 0 ≤ Onm W n 0`,

and `onmFull_le_Onm_of_gens W n 0` reduced *that* to **exactly two** into-`O'` generator families
(Dong–Jiang `O'' ⊆ O'`, `O''' ⊆ O'`):

  `hAssoc : ∀ p₁ p₂ p₃ a b c v, assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0`   (DJ Lemma 2.6),
  `hLevel : ∀ p a v g, g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0`        (DJ Lemma 2.7).

The two sibling files closed those two families *modulo a single precise residue core each*:

* `assocDefect_collapse_of_core` (`ZhuVermaAnArchCollapseAssoc`) — `hAssoc` from `CollapseAssocCore W n`
  (the full `∀ p₁ p₂ p₃ a b c v` statement, by the complete trilinear/homogeneous-decomposition
  reduction; the only residue carried is the inner `(i,j)` double-residue Borcherds-iterate scalar
  identity `CollapseAssocCore`, the `m = 0` sibling of the project-wide open `AssocScalarCore`);
* `hLevel_of_levelMixCollapse` (`ZhuVermaAnArchCollapseLevel`) — `hLevel` from the per-`p` residue
  `LevelMixCollapse W n p` (the full `∀ p a v g` statement, by the `span_le` reduction over
  `Onm W p p = span{circ} ⊔ OnmL`; the only residue carried is the two-slice `LevelMixCollapse`, the
  `OnmFull → Onm` collapse on the level-mixing output shape — equivalently the DJ 2.6 iterate
  reassociation, structurally **shared** with the `hAssoc` core).

## What this file assembles (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`CollapseCores W`** — the `Prop` bundling the two genuine residue cores at every level: the
  associator core `∀ n, CollapseAssocCore W n` and the level-mixing core `∀ n p, LevelMixCollapse W n p`.
  This is the **single precise residual** to which the entire collapse is reduced.  It is NOT an
  axiom and NOT `sorry`'d.

* **`onmCollapses_of_cores`** — `CollapseCores W ⟹ ∀ n, OnmCollapses W n`.  Wires the two closed
  reductions `assocDefect_collapse_of_core` (hAssoc) and `hLevel_of_levelMixCollapse` (hLevel) into the
  proven `onmFull_le_Onm_of_gens W n 0`, producing the collapse at every level.  FULLY proven.

* **`mUGradedAction_of_cores`** — `CollapseCores W ⟹ MUGradedAction W`.  The direct route: the collapse
  at every level gives BOTH `MUGradedAction` conjuncts (`anmRightModule_of_collapse` +
  `anmCrossClosure_of_collapse`); no `DJ28IntoFull` hypothesis is needed.  FULLY proven.

* **`zhuBijection_champions`** — the honest headline of the endgame: the faithful Zhu bijection
  `Function.Bijective (forwardMapIrr W)` from the full `FaithfulScorecard W` (which carries the deep
  hypothesis bundle fields `A`, `hirr`, `F`, `hiso`, `G`).  This is `FaithfulScorecard.bijectiveIrr` — it does
  NOT change the conditionality; it is the precise statement of the main theorem that the collapse fragment
  feeds into via the `q_act`/`MUGradedAction` substrate.

## Is the main theorem unconditional? No.

`Function.Bijective (forwardMapIrr W)` is **NOT** a closed unconditional term, for two independent
reasons:

1. **The collapse is one precise residual away.**  `onmCollapses_of_cores` discharges the entire
   collapse (hence `MUGradedAction`) from `CollapseCores W`, but `CollapseCores W` is the genuine open
   Borcherds-iterate combinatorics: the `m = 0` associator scalar core `CollapseAssocCore` (the sibling
   of the project-wide open `AssocScalarCore`) and the level-mixing `OnmFull → Onm` slice
   `LevelMixCollapse`.  These are carried as a precise `Prop`, never an axiom/`sorry`/`pbw`.

2. **The bijection needs the whole hypothesis bundle, not just `MUGradedAction`.**  Even granting
   `MUGradedAction W` (i.e. granting `CollapseCores W`), `forwardMapIrr_bijective` still rests on the
   genuine deep `FaithfulScorecard` fields `A : InducedAssignment W` (ρ on `M(U)`, bottom survival,
   functoriality), `hirr : RealizeIrreducible`, the `L(U)`-family `F`, `hiso` (`isoInvariant`), and the
   remaining fields of `G : GenFromBottomFinalFamily` (`β`/`hβ`, `bottom_ne_zero`/`BottomOrbit`,
   `kerData`/`KerJData`, `hq`, `hJ`).  `MUGradedAction` is **only** the `q_act` substrate of `G`.

So the main theorem is **the two residue cores `CollapseCores W` PLUS the deep hypothesis bundle** away — emphatically
not "one inclusion away" *for the bijection*, though it **is** exactly the two cores away *for the
collapse `OnmCollapses`/`MUGradedAction`*.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Lemmas 2.6, 2.7, 2.8, Prop 5.2; Gannon
§5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The single precise residual — the two Borcherds-iterate residue cores. -/

/-- **`CollapseCores W`** — the precise remaining residual of the entire hinge collapse, bundled at
every level.  Two fields:

* `assoc` — `∀ n, CollapseAssocCore W n`: the `m = 0` associator scalar core (DJ Lemma 2.6's inner
  `(i,j)` double-residue Borcherds-iterate identity; the sibling of the project-wide open
  `AssocScalarCore`).  Source: `ZhuVermaAnArchCollapseAssoc`.
* `level` — `∀ n p, LevelMixCollapse W n p`: the level-mixing `OnmFull → Onm` slice (DJ Lemma 2.7
  into-`O'`; the two `O'_{p,p}` generator slices, equivalently the shared DJ 2.6 iterate
  reassociation).  Source: `ZhuVermaAnArchCollapseLevel`.

This is NOT an axiom and NOT `sorry`'d: it is the genuine combinatorial content, isolated by the two
fully-proven reductions below to exactly these cores. -/
structure CollapseCores (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- The `m = 0` associator scalar core at every level (DJ Lemma 2.6 inner residue identity). -/
  assoc : ∀ n : ℕ, CollapseAssocCore W n
  /-- The level-mixing into-`O'` slice at every level/source-level (DJ Lemma 2.7). -/
  level : ∀ n p : ℕ, LevelMixCollapse W n p

/-! ## The collapse `OnmCollapses` from the two cores (FULLY proven). -/

/-- **The hinge collapse at a single level from the two cores.**  Wires the two FULLY-PROVEN
reductions — `assocDefect_collapse_of_core` (the `hAssoc` family from `CollapseAssocCore W n`) and
`hLevel_of_levelMixCollapse` (the `hLevel` family from `∀ p, LevelMixCollapse W n p`) — into the
proven `onmFull_le_Onm_of_gens W n 0`, yielding `OnmFull W n 0 ≤ Onm W n 0 = OnmCollapses W n`. -/
theorem onmCollapses_of_cores_at (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hassoc : CollapseAssocCore W n) (hlevel : ∀ p : ℕ, LevelMixCollapse W n p) :
    OnmCollapses W n :=
  onmFull_le_Onm_of_gens W n 0
    (assocDefect_collapse_of_core W n hassoc)
    (hLevel_of_levelMixCollapse W n hlevel)

/-- **The hinge collapse at every level from `CollapseCores W`.** -/
theorem onmCollapses_of_cores (W : VertexOperatorAlgebra 𝒱) (h : CollapseCores W) :
    ∀ n : ℕ, OnmCollapses W n :=
  fun n => onmCollapses_of_cores_at W n (h.assoc n) (h.level n)

/-! ## `MUGradedAction` from the two cores (FULLY proven; the direct route, no `DJ28IntoFull`). -/

/-- **The Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` from `CollapseCores W`.**

`MUGradedAction W = ∀ n, AnmRightModule W n ∧ AnmCrossClosure W n` (`ZhuVermaAnArchMU`).  From the
collapse at every level (`onmCollapses_of_cores`) BOTH conjuncts follow directly:

* `AnmRightModule W n` — `anmRightModule_of_collapse` (the proven unconditional DJ 2.8 RIGHT inclusion
  `anmRight_OnmFull_unconditional`, then the collapse);
* `AnmCrossClosure W n` — `anmCrossClosure_of_collapse` (the proven Vandermonde-free DJ 2.8 LEFT
  inclusion `anmRight_zero_OnmFull_cross`, then the collapse).

No `DJ28IntoFull` hypothesis and no cross-circle Vandermonde: DJ carries levels by associativity
defects.  This is the `q_act` substrate of the universal-property hypothesis bundle. -/
theorem mUGradedAction_of_cores (W : VertexOperatorAlgebra 𝒱) (h : CollapseCores W) :
    MUGradedAction W :=
  fun n =>
    ⟨anmRightModule_of_collapse W n (onmCollapses_of_cores W h n),
     anmCrossClosure_of_collapse W n (onmCollapses_of_cores W h n)⟩

/-! ## The honest headline — the faithful main theorem and its EXACT residual. -/

/-- **`zhuBijection_champions` — the faithful Zhu bijection, honestly conditioned.**

`Function.Bijective (forwardMapIrr W)` (Gannon Thm 5.3.4, the faithful `Φ(𝒱) ↔ Irr A(𝒱)`),
delivered from the full `FaithfulScorecard W` via the proven `FaithfulScorecard.bijectiveIrr`.

This is the precise statement of the main theorem.  It is **NOT** unconditional:

* The collapse substrate `MUGradedAction W` (the `q_act` field of the hypothesis bundle's `G`) is one precise
  residual away — `mUGradedAction_of_cores` discharges it from `CollapseCores W` (the two
  Borcherds-iterate residue cores), but `CollapseCores W` is genuinely open.
* Even granting `CollapseCores W`, the bijection still rests on the remaining deep hypothesis bundle fields
  (`A`, `hirr`, `F`, `hiso`, and the non-`q_act` fields of `G`), which are carried in `S` and are not
  discharged here.

The collapse fragment (`onmCollapses_of_cores`, `mUGradedAction_of_cores`) is the maximal assembled
piece of the endgame; this headline records exactly how it feeds the main theorem and what else the main theorem
needs. -/
theorem zhuBijection_champions (W : VertexOperatorAlgebra 𝒱) (S : FaithfulScorecard W) :
    Function.Bijective (forwardMapIrr W) :=
  S.bijectiveIrr

/-- **The collapse-fragment slice of `zhuBijection_champions`, isolated.**  Records that the two
residue cores `CollapseCores W` are precisely what discharges the `MUGradedAction` substrate of the
hypothesis bundle's `q_act` field; combined with the rest of the hypothesis bundle (which still must be supplied) it
gives the main theorem.  This makes the dependency of the main theorem on the collapse explicit: the residual
*for the collapse/`MUGradedAction`* is exactly `CollapseCores W`. -/
theorem mUGradedAction_champions (W : VertexOperatorAlgebra 𝒱) (h : CollapseCores W) :
    MUGradedAction W :=
  mUGradedAction_of_cores W h

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
