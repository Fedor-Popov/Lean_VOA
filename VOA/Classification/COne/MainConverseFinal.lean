/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bMain
import VOA.Classification.COne.McRaeO7Main
import VOA.Classification.COne.MainUnconditional
import VOA.Classification.COne.DistinctResiduals

/-! # The Gannon–Rayhaun classification of `c = 1` VOAs, all three parts

With the O5 bridge proved (`McRaeO5b.twistedJacobiBridge_holds`), the B3 route of McRae
(arXiv:1910.13226, Cor. 4.23 for `V₂`) closes:

* `finiteV2OrbifoldRationalOfC2`: for every finite `G ≤ Aut V₂` with `C₂`-cofinite `V₂^G`,
  the orbifold `V₂^G` is admissibly rational;
* `gannonRayhaunConverse_holds : GannonRayhaunConverse.{0}`: every VOA in the list is nice
  of central charge `1` (Gannon–Rayhaun Prop. 3.2);
* `gannonRayhaun_classification`: the forward theorem, the pairwise non-isomorphism, and the
  converse, as one statement.

No hypotheses. `#print axioms`: Lean's three standard axioms (the proofs use the theorem `VOA.pbw`).
-/

namespace VOA.Classification.COne

/-- The O5 bridge for every finite `G ≤ Aut V₂` with `C₂`-cofinite `V₂^G`. -/
theorem twistedJacobiBridgeAll_holds : McRaeO7.TwistedJacobiBridgeAll := by
  intro G _ hC2
  exact McRaeO5b.twistedJacobiBridge_holds G _ hC2

/-- **McRae Cor. 4.23 for `V₂`**: `C₂`-cofinite finite orbifolds of `V₂` are rational. -/
theorem finiteV2OrbifoldRationalOfC2 : FiniteV2OrbifoldRationalOfC2Fact :=
  McRaeO7.finiteV2OrbifoldRationalOfC2_of_bridge twistedJacobiBridgeAll_holds

/-- **The converse of Gannon–Rayhaun** (Prop. 3.2): every listed VOA is nice, `c = 1`. -/
theorem gannonRayhaunConverse_holds : GannonRayhaunConverse.{0} :=
  McRaeO7.gannonRayhaunConverse_of_bridge twistedJacobiBridgeAll_holds

/-- **Gannon–Rayhaun Theorem 3.1 and Proposition 3.2**: the nice VOAs of central charge `1`
are exactly `V_{2m}` (`m ≥ 1`), `V_{2m}⁺` (`m ≥ 2`), `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}`, pairwise
non-isomorphic. -/
theorem gannonRayhaun_classification :
    GannonRayhaunStatement.{0} ∧ GannonRayhaunDistinct.{0} ∧ GannonRayhaunConverse.{0} :=
  ⟨gannonRayhaun_forward, gannonRayhaunDistinct, gannonRayhaunConverse_holds⟩

end VOA.Classification.COne
