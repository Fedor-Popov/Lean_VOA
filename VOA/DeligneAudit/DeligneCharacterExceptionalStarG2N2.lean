/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalAssembly
import VOA.DeligneAudit.DeligneCharacterExceptionalZero
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N0
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N1
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M2N0

/-! One fixed-2 G2 star diagnostic from opaque coefficient certificates. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_g2_star_n2 :
    (demazureSumCoeff g2DemazureHilb 2 : ℚ) = mldeCoeff 4 2 := by
  rw [exceptional_dsum_2, exceptional_g2_m0_n2, exceptional_g2_m1_n0, 
    exceptional_g2_m1_n1, exceptional_g2_m2_n0]
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter
