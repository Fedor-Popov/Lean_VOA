/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedF4

/-! A coefficient of the independently certified finite algorithm output. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_f4_m1_n2 : f4DemazureHilb 1 2 = 0 := by
  exact exceptional_alias_coefficient f4DemazureHilb cartanF4 thetaF4 wordF4
    (fun m N => rfl) 1 2 exceptionalF4State16 0
    exceptional_f4_char_one (by decide +kernel)

end VOA.DeligneAudit.DeligneCharacter
