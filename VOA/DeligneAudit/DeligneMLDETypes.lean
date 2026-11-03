/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDEBlock
import VOA.DeligneAudit.DeligneCharacterExceptional

/-!
# The MLDE route to the targets, type by type

For every Deligne type, the character target is `TargetLowerBoundQ W (mldeCoeff h∨)`
(`XTargetLowerBound W`).  By `targetLowerBoundQ_of_vacuumQuarticRelation` it follows from

* `c(W) = -2(h∨+1)` (true for `L_k(g)`, `k = -1 - h∨/6`: `c = k dim g/(k+h∨)` with
  `dim g = 2(h∨+1)(5h∨-6)/(h∨+6)`);
* `|0⟩ ≠ 0`;
* the weight-four trace identity `VacuumQuarticRelation W κ` for some `κ` (forced to
  `(h∨+1)(5h∨-6)`).

There is no type-specific q-series identity on this side: the target is `mldeCoeff h∨` itself.
-/

namespace VOA.DeligneAudit.DeligneMLDE

open VertexOperatorAlgebra DeligneCharacter

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V) {κ : ℂ}

theorem g2TargetLowerBound_of_quartic (hc : W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) : G2TargetLowerBound W :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 4 hc hvac hrel

theorem f4TargetLowerBound_of_quartic (hc : W.centralCharge = -2 * (((9 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) : F4TargetLowerBound W :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 9 hc hvac hrel

theorem e6TargetLowerBound_of_quartic (hc : W.centralCharge = -2 * (((12 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) : E6TargetLowerBound W :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 12 hc hvac hrel

theorem e7TargetLowerBound_of_quartic (hc : W.centralCharge = -2 * (((18 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) : E7TargetLowerBound W :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 18 hc hvac hrel

theorem e8TargetLowerBound_of_quartic (hc : W.centralCharge = -2 * (((30 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) : E8TargetLowerBound W :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 30 hc hvac hrel

/-- `D₄` (`h∨ = 6`): the graded dimensions are `mldeCoeff 6` (the `D4TargetLowerBound` is stated
against `d4TargetCoeff`; the bridge is the `d4SchurQ_eq_mldeCoeff`). -/
theorem d4_targetLowerBoundQ_of_quartic (hc : W.centralCharge = -2 * (((6 : ℕ) : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) (hrel : VacuumQuarticRelation W κ) :
    TargetLowerBoundQ W (mldeCoeff 6) :=
  targetLowerBoundQ_of_vacuumQuarticRelation W 6 hc hvac hrel

end VOA.DeligneAudit.DeligneMLDE

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.e8TargetLowerBound_of_quartic
end AxiomAudit
