/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalAssembly
import VOA.DeligneAudit.DeligneCharacterExceptionalZero

/-! One fixed-0 F4 star diagnostic from opaque coefficient certificates. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_f4_star_n0 :
    (demazureSumCoeff f4DemazureHilb 0 : ℚ) = mldeCoeff 9 0 := by
  rw [exceptional_dsum_0, exceptional_f4_m0_n0]
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
