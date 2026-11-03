/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified E6 algorithm transition, stage 21. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_e6_step_21 :
    demazureFin cartanE6 1 exceptionalE6State21 = exceptionalE6State22 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
