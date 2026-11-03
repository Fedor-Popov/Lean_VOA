/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified G2 algorithm transition, stage 1. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_step_01 :
    demazureFin cartanG2 1 exceptionalG2State1 = exceptionalG2State2 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
