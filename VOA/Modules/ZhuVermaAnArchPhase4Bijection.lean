/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchStructuralClose
import VOA.Modules.ZhuVermaAnArchCrossCircReduce

/-!
# The complete Phase-4 surface — Zhu Theorem 5.3.4 modulo exactly two named residues

Everything of Zhu Theorem 5.3.4's bijection `Φ(𝒱) ↔ Irr A(𝒱)` between the two halves is a
proven, axiom-clean term:

* **the round-trip** `forwardMap ∘ invFun = id` (`ZhuInduced`);
* **functoriality `hiso`** — DJ Prop 3.4 (`MUActionNatural`) + DJ Prop 3.5 (`MUJNatural`) + the
  maximal-`J` identity `J = Jcanon` (all proven);
* **the maximal-`J` machinery** — `J`/`J_graded`/`bottom_disjoint`/`quot_submodule_graded`
  (`L₀`-semisimplicity)/`quot_graded_simple` (all terms);
* **the whole assembly** — `bijection_of_structural` (`ZhuVermaAnArchStructuralClose`), which turns
  a keystone `NeededSliceMems W` and a construction bundle `StructuralData W` into the bijection.

This file states the **single top-level Phase-4 theorem** `zhu534_bijection`, exhibiting the entire
bijection as a term modulo **exactly two** named hypotheses — the two genuine deep residues, one per
half:

* **Half A — the keystone** `crossCirc :`
  `∀ n a c d, anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` (the DJ Lemma 2.8 LEFT inclusion of
  the level-`0` inner circle into the partial ideal `Onm W n 0`).  The whole A-direction
  `MUGradedAction`/`NeededSliceMems` reduces to this single membership family
  (`neededSliceMems_of_crossCirc`).
* **Half B — the construction** `sd : StructuralData W` (`⟨A, hirr, G, bregen, G'⟩`): the genuine
  Frenkel–Zhu/DLM generalized-Verma `M(U)` construction — the admissible loop-representation `G`
  (its Borcherds relations `hderiv`/`hbracket`, iterate `hmi`, …), generation-from-bottom `bregen`,
  and the lift `G'`/`A`/`hirr`.

Both residues are the **actual Frenkel–Zhu/DLM/Dong–Jiang mathematics**, engine-verified on the
rank-1 free boson but with no closed-form witness (Half A) and requiring the full generalized-Verma
construction (Half B).  They are carried as honest hypotheses — **never** axioms, **never** `sorry`.
The bijection row is therefore **not** flipped: it would be false to claim it unconditionally.

## References
Dong–Jiang, Math. Z. 259 (2008) Lemma 2.8, Thm 4.13, Prop 3.4/3.5; Dong–Li–Mason J. Algebra 206
(1998); Frenkel–Zhu (generalized Verma); Zhu J. AMS 9 (1996); Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchStructuralClose` (`bijection_of_structural`, `StructuralData`),
`ZhuVermaAnArchCrossCircReduce` (`neededSliceMems_of_crossCirc`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`zhu534_bijection` — the complete Zhu bijection of Zhu Theorem 5.3.4, resting on exactly
the two genuine deep residues.**

From
* `hcross` — **Half A**, the keystone level-`0` inner-circle membership
  `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` (the whole `MUGradedAction`/`NeededSliceMems`
  A-direction reduces to this via `neededSliceMems_of_crossCirc`), and
* `sd` — **Half B**, the `StructuralData W` bundle (the genuine generalized-Verma `M(U)`
  construction: the admissible loop-representation `G`, generation-from-bottom `bregen`, the lift
  `G'`, and the lifting datum `A`/`hirr`),

the faithful forward map `forwardMapIrr W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, restricted to
*irreducible* iso-classes, is a **bijection**.

Everything between these two residues and the conclusion — the round-trip, functoriality `hiso`, the
maximal-`J` machinery, and the full assembly — is a proven, axiom-clean term.  The
two residues are honest carried hypotheses (the genuine deep Frenkel–Zhu/DLM content); this theorem
is **not** an unconditional flip of the bijection row. -/
theorem zhu534_bijection (W : VertexOperatorAlgebra 𝒱)
    (hcross : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0)
    (sd : InducedAssignment.StructuralData W) :
    Function.Bijective (forwardMapIrr W) :=
  bijection_of_structural (neededSliceMems_of_crossCirc W hcross) sd

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
