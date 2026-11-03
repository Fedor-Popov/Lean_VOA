/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified F4 algorithm transition, stage 14. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_f4_step_14 :
    demazureFin cartanF4 1 exceptionalF4State14 = exceptionalF4State15 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
