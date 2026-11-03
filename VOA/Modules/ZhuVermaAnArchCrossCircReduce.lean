/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcircV
import VOA.Modules.ZhuVermaAnArchDJ28IntoFull

/-!
# The keystone `hslice`/`MUGradedAction`, reduced to the SINGLE cross-circle family.

The faithful Zhu-5.3.4 bijection (`bijection_of_structural`, `ZhuVermaAnArchStructuralClose`) consumes
the keystone `hslice : NeededSliceMems W` — three `m = 0` DJ-2.8 `𝒱`-action membership families into
the partial ideal `Onm W n 0`: `circ`, `crossCirc`, `crossL`.  Two of the three are already discharged
theorems, so the keystone collapses to a single genuine membership obligation:

* **`circ`** (`∀ n c d v, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0`) is the PROVEN diagonal
  right-module closure `hcirc_closed` (`ZhuVermaAnArchMUcircV`, from the axiom-clean universal tower
  `AnmCircTowerEq_holds`).  The diagonal circle is a *level-`n`* circle (pole `n+2`) and collapses onto
  a clean grade-`M` level-`n` `c`-tower — no cross-base reorganization.
* **`crossL`** (`∀ n a c, anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0`) reduces to `crossCirc` at
  `d = 𝟙` via `anmLgen W 0 0 c = anmCirc W 0 0 c 𝟙` (`anmCirc00_vac`), already packaged in
  `neededSliceMems_of_two`.

So the entire remaining A-direction content of Zhu Thm 5.3.4 is the ONE cross-circle family

  `crossCirc :  ∀ n a c d,  anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`,

the DJ Lemma 2.8 LEFT inclusion of the *level-`0`* inner circle (pole `2`) into the partial ideal.
Unlike the diagonal circle, the level-`0` circle is NOT per-base a level-`n` `c`-tower: the pole-`2`
weight is off the level-`n` window, and the `n`-offset is only absorbed by a cross-base reorganization
into the negative-`s` creation products `c₍s₎a` — the open `ARDTowerDecomp` / `AoutUCoreLev0Core` core
(`ZhuVermaAnArchCrossCFirstGate`, `-AoutUCore`), engine-verified TRUE on the rank-1 free boson but with
no closed-form witness.  That single family is the genuine remaining wall; everything else in `hslice`
is a term.

No `sorry`/`admit`/`axiom`/`pbw`/`native_decide`.  All results
`#print axioms = [propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchMUcircV` (`hcirc_closed`, `AnmCircTowerEq_holds`),
`ZhuVermaAnArchDJ28IntoFull` (`neededSliceMems_of_two`),
`ZhuVermaAnArchHingeCollapse` (`NeededSliceMems`, `mUGradedAction_of_neededSlice`).
-/

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`NeededSliceMems W` from ONLY the cross-circle family.**  The diagonal `circ` field is the proven
`hcirc_closed`; the `crossL` field reduces to `crossCirc` (`d = 𝟙`) inside `neededSliceMems_of_two`.
So the keystone `hslice` of `bijection_of_structural` rests on the single membership family
`crossCirc :  ∀ n a c d, anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`. -/
theorem neededSliceMems_of_crossCirc (W : VertexOperatorAlgebra 𝒱)
    (hcross : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0) :
    NeededSliceMems W :=
  neededSliceMems_of_two W (hcirc_closed W) hcross

/-- **The full `MUGradedAction W` from ONLY the cross-circle membership family.**  Composes
`neededSliceMems_of_crossCirc` with the proven `mUGradedAction_of_neededSlice`
(`ZhuVermaAnArchHingeCollapse`).  This is the tightest statement of the A-direction keystone: the
Dong–Jiang `M(U)` graded-action crux (`MUGradedAction W`, the `q_act` source of the Zhu-5.3.4
bijection) follows from the single cross-circle inclusion `𝒱 *^n_0 (c ∘^0_0 d) ⊆ O'_{n,0}`. -/
theorem mUGradedAction_of_crossCirc (W : VertexOperatorAlgebra 𝒱)
    (hcross : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0) :
    MUGradedAction W :=
  mUGradedAction_of_neededSlice W (neededSliceMems_of_crossCirc W hcross)

end VOA

-- Integrity gate (axiom-clean: [propext, Classical.choice, Quot.sound]; NO sorryAx/pbw).
