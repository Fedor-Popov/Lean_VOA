/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullBracketClose
import VOA.Modules.ZhuVermaAnArchMUFullLW
import VOA.Modules.ZhuVermaAnArchIterateNonneg

/-!
# Scaffold: `M(U)` as a `WeakModule`/`LWModule` modulo **exactly one** hypothesis

With `mUFullBracket_holds` (DJ Lemma 4.7) proved, `muFullRhoU W U` is an unconditional
`V̂`-representation, and truncation/vacuum are already discharged (`muFullActModeTruncated`,
`muFullVacuumCreation`).  So the whole `M(U)` module structure rests on the **single** residual

  `hit : ModuleIterate (muFullRhoU W U)`

and, by `moduleIterate_nonneg` (`ZhuVermaAnArchIterateNonneg`), only its `ℓ < 0` regime carries any
content — the `ℓ ≥ 0` half is free.

This file wires that single hypothesis straight through to the top of the chain, so that the instant
the residual lands everything below collapses with no further work:

* `muFullActModeTruncatedU` / `muFullVacuumCreationU` — the two discharged inputs, at `muFullRhoU`;
* `muFullWeakU hit : WeakModule W (MUFull W U)`;
* `buildMUFullModuleDataU hit hL0 hfin hbot : MUFullModuleData W U h`;
* `muFullLWModuleU …  : LWModule W` — DJ's `M(U)` as a bundled lowest-weight `𝒱`-module.

Nothing here is a new mathematical claim: it is the minimal-surface repackaging that names the exact
remaining input.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Thm 4.10); `ZhuVermaAnArchMUFullBracketClose` (`mUFullBracket_holds`,
`muFullRhoU`), `ZhuVermaAnArchMUFullLW` (`muFullWeak`, `MUFullModuleData`, `buildMUFullModuleData`),
`ZhuVermaAnArchIterateNonneg` (`moduleIterate_nonneg`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two already-discharged inputs, at the unconditional representation. -/

/-- DJ Lemma 4.6(1) at `muFullRhoU` — unconditional. -/
theorem muFullActModeTruncatedU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    ActModeTruncated (muFullRhoU W U) :=
  muFullActModeTruncated W U (mUFullBracket_holds W U)

/-- DJ Lemma 4.6(2) at `muFullRhoU` — unconditional. -/
theorem muFullVacuumCreationU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    VacuumCreation (muFullRhoU W U) :=
  muFullVacuumCreation W U (mUFullBracket_holds W U)

/-! ## The module structure, modulo the single residual. -/

/-- **`M(U)` is a weak `𝒱`-module, modulo exactly `ModuleIterate`.**  Every other input of
Dong–Jiang's Theorem 4.10 — truncation (4.6(1)), the vacuum normalization (4.6(2)), the mode
translation relation, and the commutator formula (4.7) — is discharged. -/
noncomputable def muFullWeakU (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hit : ModuleIterate (muFullRhoU W U)) : WeakModule W (MUFull W U) :=
  muFullWeak W U (mUFullBracket_holds W U) hit

@[simp] theorem muFullWeakU_act (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hit : ModuleIterate (muFullRhoU W U)) (a : 𝒱) (m : ℤ) (x : MUFull W U) :
    (muFullWeakU W U hit).act a m x = muFullMode W U m a x :=
  muFullWeak_act W U (mUFullBracket_holds W U) hit a m x

/-- **`M(U)`'s graded module datum**, modulo `ModuleIterate` and the three standard graded-packaging
fields (`L₀`-scalar, finiteness of the graded pieces, bottom nonvanishing). -/
noncomputable def buildMUFullModuleDataU {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}
    (hit : ModuleIterate (muFullRhoU W U))
    (hL0 : ∀ (n : ℕ) (x : MUFull W U), x ∈ MUFull.deg W U n →
      muFullMode W U 1 W.conformalVector x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MUFull.deg W U n))
    (hbot : MUFull.deg W U 0 ≠ ⊥) :
    MUFullModuleData W U h :=
  buildMUFullModuleData (mUFullBracket_holds W U) hit hL0 hfin hbot

/-- **DJ's `M(U)` as a bundled lowest-weight `𝒱`-module**, modulo `ModuleIterate` and the three
graded-packaging fields.  This is the hard-direction object `U ↦ M(U)` of Zhu Theorem 5.3.4, on
Dong–Jiang's genuine (full) ideal. -/
noncomputable def muFullLWModuleU {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}
    (hit : ModuleIterate (muFullRhoU W U))
    (hL0 : ∀ (n : ℕ) (x : MUFull W U), x ∈ MUFull.deg W U n →
      muFullMode W U 1 W.conformalVector x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MUFull.deg W U n))
    (hbot : MUFull.deg W U 0 ≠ ⊥) :
    LWModule W :=
  (buildMUFullModuleDataU hit hL0 hfin hbot).toLWModule

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.muFullActModeTruncatedU
  #print axioms VOA.muFullVacuumCreationU
  #print axioms VOA.muFullWeakU
  #print axioms VOA.buildMUFullModuleDataU
  #print axioms VOA.muFullLWModuleU
-/
