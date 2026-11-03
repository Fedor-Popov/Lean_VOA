/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedG2

/-! A coefficient of the independently certified finite algorithm output. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_m1_n0 : g2DemazureHilb 1 0 = 14 := by
  exact exceptional_alias_coefficient g2DemazureHilb cartanG2 thetaG2 wordG2
    (fun m N => rfl) 1 0 exceptionalG2State6 14
    exceptional_g2_char_one (by decide +kernel)

end VOA.DeligneAudit.DeligneCharacter
