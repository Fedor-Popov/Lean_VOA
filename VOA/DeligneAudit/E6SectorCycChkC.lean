/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorChecks
import VOA.DeligneAudit.E6SectorDefs

set_option linter.style.longLine false

/-!
# E₆ coadjoint cyclicity: Boolean word checks (light imports)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

theorem cycChk26 : zeroL (wordS e6T 78 [77, 62] [(77, 1)] ++ scale (-(1)) [(26, 1)]) = true := by
  decide +kernel

theorem cycChk27 : zeroL (wordS e6T 78 [77, 63] [(77, 1)] ++ scale (-(1)) [(27, 1)]) = true := by
  decide +kernel

theorem cycChk28 : zeroL (wordS e6T 78 [77, 64] [(77, 1)] ++ scale (-(1)) [(28, 1)]) = true := by
  decide +kernel

theorem cycChk29 : zeroL (wordS e6T 78 [76, 68] [(77, 1)] ++ scale (-(-1)) [(29, 1)]) = true := by
  decide +kernel

theorem cycChk30 : zeroL (wordS e6T 78 [77, 66] [(77, 1)] ++ scale (-(1)) [(30, 1)]) = true := by
  decide +kernel

theorem cycChk31 : zeroL (wordS e6T 78 [77, 67] [(77, 1)] ++ scale (-(1)) [(31, 1)]) = true := by
  decide +kernel

theorem cycChk32 : zeroL (wordS e6T 78 [77, 68] [(77, 1)] ++ scale (-(1)) [(32, 1)]) = true := by
  decide +kernel

theorem cycChk33 : zeroL (wordS e6T 78 [77, 69] [(77, 1)] ++ scale (-(1)) [(33, 1)]) = true := by
  decide +kernel

theorem cycChk34 : zeroL (wordS e6T 78 [77, 70] [(77, 1)] ++ scale (-(1)) [(34, 1)]) = true := by
  decide +kernel

theorem cycChk35 : zeroL (wordS e6T 78 [77, 71] [(77, 1)] ++ scale (-(1)) [(35, 1)]) = true := by
  decide +kernel

theorem cycChk36 : zeroL (wordS e6T 78 [77, 72] [(77, 1)] ++ scale (-(1)) [(36, 1)]) = true := by
  decide +kernel

theorem cycChk37 : zeroL (wordS e6T 78 [77, 73] [(77, 1)] ++ scale (-(1)) [(37, 1)]) = true := by
  decide +kernel

theorem cycChk38 : zeroL (wordS e6T 78 [77, 74] [(77, 1)] ++ scale (-(1)) [(38, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
