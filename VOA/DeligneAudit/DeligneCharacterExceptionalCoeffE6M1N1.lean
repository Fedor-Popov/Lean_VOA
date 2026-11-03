/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedE6

/-! A coefficient of the independently certified finite algorithm output. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_e6_m1_n1 : e6DemazureHilb 1 1 = 1 := by
  exact exceptional_alias_coefficient e6DemazureHilb cartanE6 thetaE6 wordE6
    (fun m N => rfl) 1 1 exceptionalE6State22 1
    exceptional_e6_char_one (by decide +kernel)

end VOA.DeligneAudit.DeligneCharacter
