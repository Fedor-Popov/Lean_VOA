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

theorem cycChk65 : zeroL (wordS e6T 78 [64, 46] [(77, 1)] ++ scale (-(1)) [(65, 1)]) = true := by
  decide +kernel

theorem cycChk66 : zeroL (wordS e6T 78 [67] [(77, 1)] ++ scale (-(1)) [(66, 1)]) = true := by
  decide +kernel

theorem cycChk67 : zeroL (wordS e6T 78 [66] [(77, 1)] ++ scale (-(-1)) [(67, 1)]) = true := by
  decide +kernel

theorem cycChk68 : zeroL (wordS e6T 78 [64] [(77, 1)] ++ scale (-(-1)) [(68, 1)]) = true := by
  decide +kernel

theorem cycChk69 : zeroL (wordS e6T 78 [63] [(77, 1)] ++ scale (-(-1)) [(69, 1)]) = true := by
  decide +kernel

theorem cycChk70 : zeroL (wordS e6T 78 [62] [(77, 1)] ++ scale (-(1)) [(70, 1)]) = true := by
  decide +kernel

theorem cycChk71 : zeroL (wordS e6T 78 [60] [(77, 1)] ++ scale (-(1)) [(71, 1)]) = true := by
  decide +kernel

theorem cycChk72 : zeroL (wordS e6T 78 [59] [(77, 1)] ++ scale (-(1)) [(72, 1)]) = true := by
  decide +kernel

theorem cycChk73 : zeroL (wordS e6T 78 [56] [(77, 1)] ++ scale (-(-1)) [(73, 1)]) = true := by
  decide +kernel

theorem cycChk74 : zeroL (wordS e6T 78 [55] [(77, 1)] ++ scale (-(-1)) [(74, 1)]) = true := by
  decide +kernel

theorem cycChk75 : zeroL (wordS e6T 78 [51] [(77, 1)] ++ scale (-(1)) [(75, 1)]) = true := by
  decide +kernel

theorem cycChk76 : zeroL (wordS e6T 78 [46] [(77, 1)] ++ scale (-(1)) [(76, 1)]) = true := by
  decide +kernel

theorem cycChk77 : zeroL (wordS e6T 78 [] [(77, 1)] ++ scale (-(1)) [(77, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
