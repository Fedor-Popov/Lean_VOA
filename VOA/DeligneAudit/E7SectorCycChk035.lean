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

theorem cycChk35 : zeroL (wordS e7T 133 [131, 105] [(132, 1)] ++ scale (-(-1)) [(35, 1)]) = true := by
  decide +kernel

theorem cycChk36 : zeroL (wordS e7T 133 [132, 99] [(132, 1)] ++ scale (-(1)) [(36, 1)]) = true := by
  decide +kernel

theorem cycChk37 : zeroL (wordS e7T 133 [132, 100] [(132, 1)] ++ scale (-(1)) [(37, 1)]) = true := by
  decide +kernel

theorem cycChk38 : zeroL (wordS e7T 133 [131, 108] [(132, 1)] ++ scale (-(-1)) [(38, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk35
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk36
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk37
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk38
