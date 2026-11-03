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

theorem cycChk52 : zeroL (wordS e6T 78 [70, 51] [(77, 1)] ++ scale (-(1)) [(52, 1)]) = true := by
  decide +kernel

theorem cycChk53 : zeroL (wordS e6T 78 [72, 46] [(77, 1)] ++ scale (-(1)) [(53, 1)]) = true := by
  decide +kernel

theorem cycChk54 : zeroL (wordS e6T 78 [71, 46] [(77, 1)] ++ scale (-(1)) [(54, 1)]) = true := by
  decide +kernel

theorem cycChk55 : zeroL (wordS e6T 78 [74] [(77, 1)] ++ scale (-(1)) [(55, 1)]) = true := by
  decide +kernel

theorem cycChk56 : zeroL (wordS e6T 78 [73] [(77, 1)] ++ scale (-(1)) [(56, 1)]) = true := by
  decide +kernel

theorem cycChk57 : zeroL (wordS e6T 78 [70, 46] [(77, 1)] ++ scale (-(1)) [(57, 1)]) = true := by
  decide +kernel

theorem cycChk58 : zeroL (wordS e6T 78 [69, 46] [(77, 1)] ++ scale (-(-1)) [(58, 1)]) = true := by
  decide +kernel

theorem cycChk59 : zeroL (wordS e6T 78 [72] [(77, 1)] ++ scale (-(-1)) [(59, 1)]) = true := by
  decide +kernel

theorem cycChk60 : zeroL (wordS e6T 78 [71] [(77, 1)] ++ scale (-(-1)) [(60, 1)]) = true := by
  decide +kernel

theorem cycChk61 : zeroL (wordS e6T 78 [67, 46] [(77, 1)] ++ scale (-(-1)) [(61, 1)]) = true := by
  decide +kernel

theorem cycChk62 : zeroL (wordS e6T 78 [70] [(77, 1)] ++ scale (-(-1)) [(62, 1)]) = true := by
  decide +kernel

theorem cycChk63 : zeroL (wordS e6T 78 [69] [(77, 1)] ++ scale (-(1)) [(63, 1)]) = true := by
  decide +kernel

theorem cycChk64 : zeroL (wordS e6T 78 [68] [(77, 1)] ++ scale (-(1)) [(64, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
