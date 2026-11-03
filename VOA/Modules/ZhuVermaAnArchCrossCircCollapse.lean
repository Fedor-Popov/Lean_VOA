/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCrossCircReduce
import VOA.Modules.ZhuVermaAnArchDJ27
import VOA.Modules.ZhuVermaAnArchCollapseChampions

/-!
# The A-direction keystone reduced to the SINGLE collapse inclusion `OnmFull ≤ Onm`

`circCross_mem` (DJ Lemma 2.7, unconditional, `ZhuVermaAnArchDJ27`) already proves the cross-circle
`𝒱`-action lands in the *full* Dong–Jiang ideal:
  `anmGen W n 0 0 a (anmCirc W 0 0 c d) ∈ OnmFull W n 0`.
The keystone `crossCirc` (`ZhuVermaAnArchCrossCircReduce`) is the *identical* statement into the
repo *partial* ideal `Onm W n 0` (`anmGen W n 0 0 = anmRight W n 0`).  Since `Onm ≤ OnmFull` always
(`Onm_le_OnmFull`), the only gap between the two is the reverse inclusion
`OnmFull W n 0 ≤ Onm W n 0` — the collapse `O''_{n,0}, O'''_{n,0} ⊆ O'_{n,0}` (`CollapseHyp`),
engine-confirmed TRUE (full-space; `assocDefect`/`levelMix` generators ∈ `Onm(1,0)`).

Consequently the ENTIRE A-direction of Zhu 5.3.4 — `MUGradedAction W`, the `q_act` source of the
bijection — follows from that single ideal inclusion, with NO appeal to `DJ28Cross`/crossCirc0:
`crossCirc` is the proven `circCross_mem` transported across the collapse.  This is the tightest
reduction of Half A currently in the repo; the remaining obligation is the honest deep residue
`OnmFull W n 0 ≤ Onm W n 0` (= `CollapseAssocCore n` + `LevelMixCollapse`, the
`AssocScalarCore`-class double-residue combinatorics), carried as a hypothesis — NOT an axiom.
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The keystone `crossCirc`, from the single collapse inclusion.**  `crossCirc` into the partial
ideal `Onm W n 0` is the proven `circCross_mem` (into `OnmFull W n 0`) transported across the
collapse inclusion `OnmFull W n 0 ≤ Onm W n 0`.  No `DJ28Cross`/crossCirc0 is needed — the `a`-outside
cross-circle is *directly* the discharged DJ Lemma 2.7 family. -/
theorem crossCirc_of_collapse (W : VertexOperatorAlgebra 𝒱)
    (hcol : ∀ n : ℕ, OnmFull W n 0 ≤ Onm W n 0) :
    ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 := by
  intro n a c d
  rw [← anmGen_eq_anmRight]
  exact hcol n (circCross_mem W n 0 0 a d c)

/-- **The full `MUGradedAction W` (Half A) from the single collapse inclusion.**  Composes
`crossCirc_of_collapse` with `mUGradedAction_of_crossCirc`.  The Dong–Jiang `M(U)` graded-action
crux (the `q_act` source of the Zhu-5.3.4 bijection) rests on the single ideal inclusion
`OnmFull W n 0 ≤ Onm W n 0` (the collapse `O''_{n,0}, O'''_{n,0} ⊆ O'_{n,0}`). -/
theorem mUGradedAction_of_collapse (W : VertexOperatorAlgebra 𝒱)
    (hcol : ∀ n : ℕ, OnmFull W n 0 ≤ Onm W n 0) : MUGradedAction W :=
  mUGradedAction_of_crossCirc W (crossCirc_of_collapse W hcol)

/-- **`mUGradedAction_of_collapse` accepts the named collapse predicate `OnmCollapses` verbatim.**
`OnmCollapses W n` unfolds to `OnmFull W n 0 ≤ Onm W n 0` (`ZhuVermaAnArchHingeCollapse`), so the
collapse fragment `onmCollapses_of_cores` (which produces `∀ n, OnmCollapses W n`) feeds this route
directly. -/
theorem mUGradedAction_of_onmCollapses (W : VertexOperatorAlgebra 𝒱)
    (hcol : ∀ n : ℕ, OnmCollapses W n) : MUGradedAction W :=
  mUGradedAction_of_collapse W hcol

/-- **Independent cross-check: `CollapseCores W ⟹ MUGradedAction W` via the single cross-circle
family.**  The existing `mUGradedAction_of_cores` derives the same conclusion through the two DJ-2.8
conjuncts (`anmRightModule_of_collapse` + `anmCrossClosure_of_collapse`); here we route instead
through the SINGLE keystone `crossCirc` (proven `circCross_mem` transported across the collapse),
composed with `onmCollapses_of_cores`.  Two independent proof paths landing the same reduction
`CollapseCores → MUGradedAction` is a strong correctness signal for the endgame wiring; the residual
is identical (`CollapseCores W`, the two Borcherds-iterate cores — which both collapse to the single
`O'' ⊆ O'` associator-defect content). -/
theorem mUGradedAction_of_cores_via_crossCirc (W : VertexOperatorAlgebra 𝒱)
    (h : CollapseCores W) : MUGradedAction W :=
  mUGradedAction_of_collapse W (onmCollapses_of_cores W h)

/-- **The ROBUST membership reduction of Half A.**  Half A
(`MUGradedAction W`, hence `hslice`) follows from the two DJ-Lemma-2.6/2.7 *into-`O'`* **membership**
families — `assocDefect ∈ Onm` (`O'' ⊆ O'`) and `levelMix ∈ Onm` (`O''' ⊆ O'`) — via the proven
reduction `onmFull_le_Onm_of_gens` (`ZhuVermaAnArchHingeCollapse`).  This is the correct target: the
membership is engine-TRUE (full-space) via a NON-canonical combination, whereas the *exact-equality*
`CollapseAssocCore` (`assocDefect = UfamAnm + VfamAnm`) is engine-DISPROVED for `n ≥ 1`.
So the `CollapseCores`/`mUGradedAction_of_cores` route rests on a hypothesis that is false as an
equality; THIS route rests on the true membership and is the one to discharge. -/
theorem mUGradedAction_of_membership (W : VertexOperatorAlgebra 𝒱)
    (hAssoc : ∀ (n p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W n 0 p₁ p₂ p₃ a b c v ∈ Onm W n 0)
    (hLevel : ∀ (n p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W n 0 p a g v ∈ Onm W n 0) :
    MUGradedAction W :=
  mUGradedAction_of_onmCollapses W fun n =>
    onmFull_le_Onm_of_gens W n 0 (hAssoc n) (hLevel n)

end VOA
