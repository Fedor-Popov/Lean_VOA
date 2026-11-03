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

theorem cycChk47 : zeroL (wordS e7T 133 [132, 110] [(132, 1)] ++ scale (-(1)) [(47, 1)]) = true := by
  decide +kernel

theorem cycChk48 : zeroL (wordS e7T 133 [131, 116] [(132, 1)] ++ scale (-(-1)) [(48, 1)]) = true := by
  decide +kernel

theorem cycChk49 : zeroL (wordS e7T 133 [132, 112] [(132, 1)] ++ scale (-(1)) [(49, 1)]) = true := by
  decide +kernel

theorem cycChk50 : zeroL (wordS e7T 133 [132, 113] [(132, 1)] ++ scale (-(1)) [(50, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7

#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk47
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk48
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk49
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.cycChk50
