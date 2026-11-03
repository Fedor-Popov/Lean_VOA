/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedG2

namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_m2_n0 : g2DemazureHilb 2 0 = 77 := by
  exact exceptional_alias_coefficient g2DemazureHilb cartanG2 thetaG2 wordG2
    (fun m N => rfl) 2 0 exceptionalG2State12 77
    exceptional_g2_char_two (by decide +kernel)

end VOA.DeligneAudit.DeligneCharacter
