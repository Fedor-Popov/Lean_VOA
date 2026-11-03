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

theorem cycChk13 : zeroL (wordS e6T 78 [76, 55] [(77, 1)] ++ scale (-(-1)) [(13, 1)]) = true := by
  decide +kernel

theorem cycChk14 : zeroL (wordS e6T 78 [76, 56] [(77, 1)] ++ scale (-(-1)) [(14, 1)]) = true := by
  decide +kernel

theorem cycChk15 : zeroL (wordS e6T 78 [77, 51] [(77, 1)] ++ scale (-(1)) [(15, 1)]) = true := by
  decide +kernel

theorem cycChk16 : zeroL (wordS e6T 78 [75, 62] [(77, 1)] ++ scale (-(-1)) [(16, 1)]) = true := by
  decide +kernel

theorem cycChk17 : zeroL (wordS e6T 78 [76, 59] [(77, 1)] ++ scale (-(-1)) [(17, 1)]) = true := by
  decide +kernel

theorem cycChk18 : zeroL (wordS e6T 78 [76, 60] [(77, 1)] ++ scale (-(-1)) [(18, 1)]) = true := by
  decide +kernel

theorem cycChk19 : zeroL (wordS e6T 78 [77, 55] [(77, 1)] ++ scale (-(1)) [(19, 1)]) = true := by
  decide +kernel

theorem cycChk20 : zeroL (wordS e6T 78 [77, 56] [(77, 1)] ++ scale (-(1)) [(20, 1)]) = true := by
  decide +kernel

theorem cycChk21 : zeroL (wordS e6T 78 [76, 62] [(77, 1)] ++ scale (-(-1)) [(21, 1)]) = true := by
  decide +kernel

theorem cycChk22 : zeroL (wordS e6T 78 [76, 63] [(77, 1)] ++ scale (-(-1)) [(22, 1)]) = true := by
  decide +kernel

theorem cycChk23 : zeroL (wordS e6T 78 [77, 59] [(77, 1)] ++ scale (-(1)) [(23, 1)]) = true := by
  decide +kernel

theorem cycChk24 : zeroL (wordS e6T 78 [77, 60] [(77, 1)] ++ scale (-(1)) [(24, 1)]) = true := by
  decide +kernel

theorem cycChk25 : zeroL (wordS e6T 78 [76, 66] [(77, 1)] ++ scale (-(-1)) [(25, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
