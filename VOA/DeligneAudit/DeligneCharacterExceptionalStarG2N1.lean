/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalAssembly
import VOA.DeligneAudit.DeligneCharacterExceptionalZero
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N0

/-! One fixed-1 G2 star diagnostic from opaque coefficient certificates. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_star_n1 :
    (demazureSumCoeff g2DemazureHilb 1 : ℚ) = mldeCoeff 4 1 := by
  rw [exceptional_dsum_1, exceptional_g2_m0_n1, exceptional_g2_m1_n0]
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
