/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalStates

/-! One certified E6 algorithm transition, stage 18. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_e6_step_18 :
    demazureFin cartanE6 2 exceptionalE6State18 = exceptionalE6State19 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
