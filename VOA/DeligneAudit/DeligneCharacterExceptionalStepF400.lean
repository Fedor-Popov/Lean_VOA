/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified F4 algorithm transition, stage 0. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_f4_step_00 :
    demazureZero cartanF4 thetaF4 (exceptionalSeed thetaF4) = exceptionalF4State1 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
