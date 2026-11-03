/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJCarrierWeak

/-!
# FINAL axiom gate for `ZhuVermaAnArchDJCarrierWeak` (C5 Phase 2)

Run with `lake env lean -DmaxSynthPendingDepth=3 scripts/audit/DJCarrierWeakAxiomAudit.lean` (a bare
`lake env lean` drops the lakefile's `maxSynthPendingDepth` and silently inserts `sorryAx` on these
nested quotient/tensor carriers).  Expected on every line:
`[propext, Classical.choice, Quot.sound]` — NO `pbw`, NO `sorryAx`, no new axiom.
-/

-- §0–§2 the translation relation
#print axioms VOA.djCarrier_end_ext
#print axioms VOA.djActGen
#print axioms VOA.djPieceAct_Lgen_zero
#print axioms VOA.djActGen_hderiv

-- §3 the Borcherds loop commutator
#print axioms VOA.assembleAct_bracket_eval
#print axioms VOA.djActGen_bracket

-- §4 the `V̂`-representation and the weak module
#print axioms VOA.djModeDataZero
#print axioms VOA.djRhoZero
#print axioms VOA.djRhoZero_actMode
#print axioms VOA.djActModeTruncated
#print axioms VOA.djVacuumCreation
#print axioms VOA.moduleIterate_djRhoZero
#print axioms VOA.isModuleJacobi_djRhoZero
#print axioms VOA.djCarrierWeak
#print axioms VOA.djCarrierWeak_act
#print axioms VOA.djCarrierWeak_mode

-- §5 the `ℕ`-grading as a module grading
#print axioms VOA.djCarrierWeak_act_deg_mem
#print axioms VOA.djCarrierWeak_act_deg_eq_zero

-- §6 the `ℂ`-weight grading and the finrank-free lowest-weight packaging
#print axioms VOA.djCWeight
#print axioms VOA.djCWeight_cast
#print axioms VOA.djCWeight_eq_bot
#print axioms VOA.djCWeight_isInternal
#print axioms VOA.djCWeight_isLow
#print axioms VOA.djCWeight_boundedBelow
#print axioms VOA.djCWeight_zero
#print axioms VOA.djGradedLW

-- §7 the bottom, threaded through the PBW datum
#print axioms VOA.djCarrierWeak_bottom_equiv
#print axioms VOA.djCarrier_deg_zero_ne_bot
#print axioms VOA.djGradedLW_of_pbwDatum
#print axioms VOA.djGradedLW_bottom_equiv

-- §8 the weak-submodule bridge and generation
#print axioms VOA.djModeStable_of_weakSubmodule
#print axioms VOA.weakSubmodule_of_djModeStable
#print axioms VOA.djCarrierWeak_generated_by_bottom
