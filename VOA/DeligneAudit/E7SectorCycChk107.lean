/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorIntegerTable
import VOA.DeligneAudit.E6SectorDefs

/-!
# `E₇` coadjoint cyclicity: Boolean word checks (depth 2 from `δ_{132}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk107 : zeroL (wordS e7T 133 [117, 76] [(132, 1)] ++ scale (-(-1)) [(107, 1)]) = true := by
  decide +kernel

theorem cycChk108 : zeroL (wordS e7T 133 [121] [(132, 1)] ++ scale (-(-1)) [(108, 1)]) = true := by
  decide +kernel

theorem cycChk109 : zeroL (wordS e7T 133 [120] [(132, 1)] ++ scale (-(-1)) [(109, 1)]) = true := by
  decide +kernel

theorem cycChk110 : zeroL (wordS e7T 133 [119] [(132, 1)] ++ scale (-(-1)) [(110, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk107
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk108
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk109
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk110
