/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcross
import VOA.Modules.ZhuVermaAnArchDJ28Term2Identity

/-!
# The whole Half-A keystone on ONE residual: `MUGradedAction W` from `CrossCircCore`.

With `Term2Level_holds` (`ZhuVermaAnArchDJ28Term2Identity`) proved unconditionally — the level-`n`-inner
half of the Dong–Jiang Lemma-2.8 keystone — the entire `M(U)` graded-action crux `MUGradedAction W`
(Half A of Zhu Thm 5.3.4) reduces to the SINGLE remaining core

  `CrossCircCore W n`  (`ZhuVermaAnArchMUcross`) :=
    `∀ K, ∀ a ∈ 𝒱_K, ∀ c d, resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`,

i.e. `Term₁ = anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` (the level-`0`-inner circle, homogeneous
`a`).  This is the cross-level circle residue that DJ's degree argument (iterate + the off-diagonal
`resHom_offdiag_mem_Onm`, DJ Lemma 2.4) reduces to the c-first ordered term `crossCirc0` — engine-TRUE,
the genuine remaining core (equivalently `anmRightDiff ∈ Onm` via the proven `circDiffAnmRight_split` +
`crossDiffComm_mem_Onm` and `Term2Level_holds`).

This main theorem records that the two-part reduction `MUGradedAction_of_TermLevels` consumes only ONE
open family: `Term2` is discharged, so `MUGradedAction W ⟸ (∀ n, CrossCircCore W n)`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), §2 (Lemmas 2.4–2.5); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`MUGradedAction W` from the single `CrossCircCore` residual** — the whole Half-A keystone, with
`Term₂` discharged by `Term2Level_holds`.  `CrossCircCore W n` gives `Term1Level W n`
(`anmRight_zero_crossCirc_mem_Onm_of_core`, homogeneous reduction); `Term2Level_holds` gives
`Term2Level W n` unconditionally; `MUGradedAction_of_TermLevels` assembles the crux.  So the entire
Dong–Jiang `M(U)` graded-action (Half A of Zhu Thm 5.3.4) rests on the single cross-level circle core
`CrossCircCore` — the level-`0`-inner residue whose off-diagonal part discharges via DJ Lemma 2.4
(`resHom_offdiag_mem_Onm`), leaving the `crossCirc0` c-first core. -/
theorem mUGradedAction_of_crossCircCore (W : VertexOperatorAlgebra 𝒱)
    (hcore : ∀ n : ℕ, CrossCircCore W n) : MUGradedAction W :=
  MUGradedAction_of_TermLevels W
    (fun n => anmRight_zero_crossCirc_mem_Onm_of_core W n (hcore n))
    (fun n => Term2Level_holds W n)

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.mUGradedAction_of_crossCircCore
-/
