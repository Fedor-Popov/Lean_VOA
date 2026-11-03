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

theorem cycChk39 : zeroL (wordS e6T 78 [77, 75] [(77, 1)] ++ scale (-(1)) [(39, 1)]) = true := by
  decide +kernel

theorem cycChk40 : zeroL (wordS e6T 78 [77, 76] [(77, 1)] ++ scale (-(1)) [(40, 1)]) = true := by
  decide +kernel

theorem cycChk41 : zeroL (wordS e6T 78 [77, 77] [(77, 1)] ++ scale (-(2)) [(41, 1)]) = true := by
  decide +kernel

theorem cycChk42 : zeroL (wordS e6T 78 [72, 55] [(77, 1)] ++ scale (-(1)) [(42, 1)]) = true := by
  decide +kernel

theorem cycChk43 : zeroL (wordS e6T 78 [74, 51] [(77, 1)] ++ scale (-(-1)) [(43, 1)]) = true := by
  decide +kernel

theorem cycChk44 : zeroL (wordS e6T 78 [75, 46] [(77, 1)] ++ scale (-(-1)) [(44, 1)]) = true := by
  decide +kernel

theorem cycChk45 : zeroL (wordS e6T 78 [73, 51] [(77, 1)] ++ scale (-(1)) [(45, 1)]) = true := by
  decide +kernel

theorem cycChk46 : zeroL (wordS e6T 78 [76] [(77, 1)] ++ scale (-(-1)) [(46, 1)]) = true := by
  decide +kernel

theorem cycChk47 : zeroL (wordS e6T 78 [70, 56] [(77, 1)] ++ scale (-(-1)) [(47, 1)]) = true := by
  decide +kernel

theorem cycChk48 : zeroL (wordS e6T 78 [72, 51] [(77, 1)] ++ scale (-(-1)) [(48, 1)]) = true := by
  decide +kernel

theorem cycChk49 : zeroL (wordS e6T 78 [74, 46] [(77, 1)] ++ scale (-(-1)) [(49, 1)]) = true := by
  decide +kernel

theorem cycChk50 : zeroL (wordS e6T 78 [73, 46] [(77, 1)] ++ scale (-(-1)) [(50, 1)]) = true := by
  decide +kernel

theorem cycChk51 : zeroL (wordS e6T 78 [75] [(77, 1)] ++ scale (-(-1)) [(51, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
