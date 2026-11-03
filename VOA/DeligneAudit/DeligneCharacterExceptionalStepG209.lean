/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified G2 algorithm transition, stage 9. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_step_09 :
    demazureFin cartanG2 1 exceptionalG2State9 = exceptionalG2State10 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
