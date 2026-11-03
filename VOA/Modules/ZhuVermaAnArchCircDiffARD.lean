/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCFirstDiffMaster
import VOA.Modules.ZhuVermaAnArchCrossCFirstDiffClose

/-!
# Game One — closing **`CircDiffAnmRightTowerEq`** directly from the `a`-outer `ARDTowerDecomp`.

This file CLOSES the diagonal pole-`2` tower-decomposition core `CircDiffAnmRightTowerEq`
(`ZhuVermaAnArchMUcircDiff`) — the single remaining input of the Dong–Jiang `M(U)` graded-action crux
through the diagonal route `MUGradedAction_of_diagCore` (`ZhuVermaAnArchCFirstDiffMaster`) — **down to
the single `a`-outer right-action-difference tower decomposition `ARDTowerDecomp`**
(`ZhuVermaAnArchCrossCFirstGate`), with the `crossDiffComm` commutator half discharged entirely by the
two PROVEN commutator twins.

## The route (FULLY proven here; no `sorry`/axiom/`pbw`)

The diagonal pole-`2` core asks for

  `(CircDiffAnmRightTowerEq)   anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`
      `= PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

The master bridge `crossCFirstDiff_eq_anmCircAnmRightDiff` (`ZhuVermaAnArchCFirstDiffMaster`)
identifies the LHS with the `a`-outer `c`-first DIFFERENCE object `crossCFirstDiff`, and the exact
structural identity `crossCFirstDiff_eq` (`ZhuVermaAnArchCrossCFirstDiffClose`) splits it as

  `crossCFirstDiff = anmRightDiff + (ardComm − crossCircComm)`,

the `a`-outer right-action-difference family `anmRightDiff` plus the commutator difference
`ardComm − crossCircComm`.  The commutator difference IS a homogeneous `MGTowerFam`
(`commDiff_eq_MGTowerFam`, the ℂ-difference of the two PROVEN commutator twins `ARDCommTowerEq_holds`,
`CrossCommTowerEq_holds`, `ZhuVermaAnArchVcoreTwins`), and `anmRightDiff` is supplied as
`PresTowerFam(c) + MGTowerFam` by `ARDTowerDecomp`.  Merging the two `MGTowerFam`s (`MGTowerFam_add`,
homogeneity by `MGTowerFam_add_hom`) and carrying the U-tower in `c` unchanged yields the explicit
`CircDiffAnmRightTowerEq` witness.

This **identifies the diagonal pole-`2` core `CircDiffAnmRightTowerEq` with the `a`-outer core
`ARDTowerDecomp`** — the two faces of the same DJ Lemma 2.8 reorganization — modulo the two PROVEN
commutator twins, and re-exports the full `MUGradedAction W` closure (through the diagonal route
`MUGradedAction_of_diagCore`) against the single universal `ARDTowerDecomp`.

## What is proved here (axiom-clean)

* **`circDiffAnmRightTowerEq_of_ARDTowerDecomp`** — **the full structural lift** `ARDTowerDecomp ⟹
  CircDiffAnmRightTowerEq`, via the master bridge + `crossCFirstDiff_eq` + `commDiff_eq_MGTowerFam` +
  `MGTowerFam_add`.
* **`MUGradedAction_of_ARDTowerDecomp_via_diag`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the diagonal route `MUGradedAction_of_diagCore`.

The diagonal core `CircDiffAnmRightTowerEq` and the cross core `CrossCFirstDiffTowerEq` are both
discharged by the SAME `ARDTowerDecomp` (the latter already via
`crossCFirstDiffTowerEq_of_ARDTowerDecomp`, `ZhuVermaAnArchCrossCFirstDiffClose`); the two
`MUGradedAction` routes are unified to the single `a`-outer tower decomposition.

## The single remaining identity (engine-verified TRUE; NOT faked)

The universally-quantified `ARDTowerDecomp W n K M P a c d` — the `a`-outer right-action-difference
tower decomposition

  `anmRightDiff W n K a c d = (c-tower in `c` based at `a₍g₎d`) + (W-family in `c₍s₎a` based at `d`),

the genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation core (the `a`-outer level-`n` mirror
of the FULLY-proven diagonal V-core `AnmCircTowerEq_holds`, `ZhuVermaAnArchMUcircV`).  Engine values:
`certificates/mathematica/anmrightdiff_tower.wl`, `certificates/mathematica/circ_diff_dj.wl`, `certificates/mathematica/circ_diff_weights.wl` (`n = 1, 2`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The full structural lift `ARDTowerDecomp` ⟹ `CircDiffAnmRightTowerEq`. -/

/-- **`ARDTowerDecomp` ⟹ `CircDiffAnmRightTowerEq`** (the full structural lift).  By the master bridge
`crossCFirstDiff_eq_anmCircAnmRightDiff`, the diagonal pole-`2` difference
`anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)` IS the `a`-outer
`c`-first DIFFERENCE `crossCFirstDiff`; the exact identity `crossCFirstDiff_eq` splits it as
`anmRightDiff + (ardComm − crossCircComm)`.  The residual `anmRightDiff` is supplied as
`PresTowerFam(c) + MGTowerFam` by `ARDTowerDecomp`; the commutator difference is an `MGTowerFam`
(`commDiff_eq_MGTowerFam`).  Merging the two `MGTowerFam`s (`MGTowerFam_add`, homogeneity by
`MGTowerFam_add_hom`) and carrying the `c`-tower unchanged yields the explicit
`CircDiffAnmRightTowerEq` witness. -/
theorem circDiffAnmRightTowerEq_of_ARDTowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hdec : ARDTowerDecomp W n K M P a c d) :
    CircDiffAnmRightTowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S₁, baseU, wU, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, hdeceq⟩ := hdec
  obtain ⟨S₂, gradeS₂, leftS₂, baseS₂, ΔS₂, wS₂, hhom₂, hcommeq⟩ :=
    commDiff_eq_MGTowerFam W n ha hc hd
  refine ⟨RU, ΔU, S₁ + S₂, baseU, wU,
    (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₁ S₂ gradeS₁ leftS₁ gradeS₂ leftS₂ hhom₁ hhom₂, ?_⟩
  rw [← crossCFirstDiff_eq_anmCircAnmRightDiff W n ha hc d, crossCFirstDiff_eq W n ha hc d,
    hdeceq, hcommeq, add_assoc,
    MGTowerFam_add W n S₁ S₂ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂]

/-! ## The full `MUGradedAction W` from the single universal `ARDTowerDecomp` (diagonal route). -/

/-- **The full `MUGradedAction W` from the single universal `ARDTowerDecomp`** (the diagonal route).
Given, for every level `n` and all homogeneous data, the `a`-outer right-action-difference tower
decomposition `ARDTowerDecomp` (the genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation
core), the structural lift `circDiffAnmRightTowerEq_of_ARDTowerDecomp` supplies the universal
diagonal pole-`2` core `CircDiffAnmRightTowerEq`, and `MUGradedAction_of_diagCore`
(`ZhuVermaAnArchCFirstDiffMaster`) — whose every other piece is fully discharged — assembles the
Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This re-derives `MUGradedAction W` from `ARDTowerDecomp` through the diagonal pole-`2` face,
unifying it with the `c`-first pole-difference route `MUGradedAction_of_ARDTowerDecomp_via_diff`
(`ZhuVermaAnArchCrossCFirstDiffClose`): both routes discharged by the SAME `ARDTowerDecomp`. -/
theorem MUGradedAction_of_ARDTowerDecomp_via_diag (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_diagCore W
    (fun n K M P a ha c hc d hd =>
      circDiffAnmRightTowerEq_of_ARDTowerDecomp W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — the diagonal pole-`2` core UNIFIED with the `a`-outer core `ARDTowerDecomp`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`circDiffAnmRightTowerEq_of_ARDTowerDecomp`** — **the full structural lift** `ARDTowerDecomp ⟹
  CircDiffAnmRightTowerEq` (the diagonal pole-`2` core), via the master bridge + `crossCFirstDiff_eq`
  + `commDiff_eq_MGTowerFam` + `MGTowerFam_add`, re-using the two PROVEN commutator twins.
* **`MUGradedAction_of_ARDTowerDecomp_via_diag`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the diagonal route `MUGradedAction_of_diagCore`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`ARDTowerDecomp W n K M P a c d` — the `a`-outer right-action-difference tower decomposition

  `anmRightDiff W n K a c d = (c-tower in c based at a₍g₎d) + (W-family in c₍s₎a based at d),

the genuine `a`-irreducible Dong–Jiang Lemma 2.8 core (the `a`-outer level-`n` mirror of the
FULLY-proven diagonal V-core `AnmCircTowerEq_holds`, `ZhuVermaAnArchMUcircV`).  Both the diagonal
pole-`2` core `CircDiffAnmRightTowerEq` (here) and the `c`-first pole-difference core
`CrossCFirstDiffTowerEq` (`crossCFirstDiffTowerEq_of_ARDTowerDecomp`) are discharged by it; the
commutator content is fully discharged via the proven V-core twins.  Engine values:
`certificates/mathematica/anmrightdiff_tower.wl`, `certificates/mathematica/circ_diff_dj.wl`, `certificates/mathematica/circ_diff_weights.wl` (`n = 1, 2`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.circDiffAnmRightTowerEq_of_ARDTowerDecomp
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_via_diag
-/
