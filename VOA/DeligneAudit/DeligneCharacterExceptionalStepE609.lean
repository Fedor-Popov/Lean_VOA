/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified E6 algorithm transition, stage 9. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_e6_step_09 :
    demazureFin cartanE6 3 exceptionalE6State9 = exceptionalE6State10 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
