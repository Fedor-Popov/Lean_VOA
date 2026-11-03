/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalParameters

/-! The seed character has only its degree-zero constant coefficient. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_m0_n0 : g2DemazureHilb 0 0 = 1 := by
  decide +kernel

theorem exceptional_g2_m0_n1 : g2DemazureHilb 0 1 = 0 := by
  decide +kernel

theorem exceptional_g2_m0_n2 : g2DemazureHilb 0 2 = 0 := by
  decide +kernel

theorem exceptional_f4_m0_n0 : f4DemazureHilb 0 0 = 1 := by
  decide +kernel

theorem exceptional_f4_m0_n1 : f4DemazureHilb 0 1 = 0 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
