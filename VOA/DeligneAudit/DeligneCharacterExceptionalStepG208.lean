/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified G2 algorithm transition, stage 8. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_step_08 :
    demazureFin cartanG2 0 exceptionalG2State8 = exceptionalG2State9 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
