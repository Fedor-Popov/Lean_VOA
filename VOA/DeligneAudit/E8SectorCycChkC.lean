/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `8..67` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk8 : zeroL (wordS e8T 248 [247, 128] [(247, 1)] ++ scale (-(-1)) [(8, 1)]) = true := by
  decide +kernel

theorem cycChk9 : zeroL (wordS e8T 248 [246, 136] [(247, 1)] ++ scale (-(-1)) [(9, 1)]) = true := by
  decide +kernel

theorem cycChk10 : zeroL (wordS e8T 248 [245, 143] [(247, 1)] ++ scale (-(1)) [(10, 1)]) = true := by
  decide +kernel

theorem cycChk11 : zeroL (wordS e8T 248 [244, 150] [(247, 1)] ++ scale (-(-1)) [(11, 1)]) = true := by
  decide +kernel

theorem cycChk12 : zeroL (wordS e8T 248 [243, 157] [(247, 1)] ++ scale (-(1)) [(12, 1)]) = true := by
  decide +kernel

theorem cycChk13 : zeroL (wordS e8T 248 [242, 164] [(247, 1)] ++ scale (-(-1)) [(13, 1)]) = true := by
  decide +kernel

theorem cycChk14 : zeroL (wordS e8T 248 [242, 165] [(247, 1)] ++ scale (-(-1)) [(14, 1)]) = true := by
  decide +kernel

theorem cycChk15 : zeroL (wordS e8T 248 [241, 174] [(247, 1)] ++ scale (-(-1)) [(15, 1)]) = true := by
  decide +kernel

theorem cycChk16 : zeroL (wordS e8T 248 [247, 136] [(247, 1)] ++ scale (-(1)) [(16, 1)]) = true := by
  decide +kernel

theorem cycChk17 : zeroL (wordS e8T 248 [246, 143] [(247, 1)] ++ scale (-(-1)) [(17, 1)]) = true := by
  decide +kernel

theorem cycChk18 : zeroL (wordS e8T 248 [245, 150] [(247, 1)] ++ scale (-(1)) [(18, 1)]) = true := by
  decide +kernel

theorem cycChk19 : zeroL (wordS e8T 248 [244, 157] [(247, 1)] ++ scale (-(-1)) [(19, 1)]) = true := by
  decide +kernel

theorem cycChk20 : zeroL (wordS e8T 248 [243, 164] [(247, 1)] ++ scale (-(1)) [(20, 1)]) = true := by
  decide +kernel

theorem cycChk21 : zeroL (wordS e8T 248 [243, 165] [(247, 1)] ++ scale (-(1)) [(21, 1)]) = true := by
  decide +kernel

theorem cycChk22 : zeroL (wordS e8T 248 [242, 174] [(247, 1)] ++ scale (-(-1)) [(22, 1)]) = true := by
  decide +kernel

theorem cycChk23 : zeroL (wordS e8T 248 [247, 143] [(247, 1)] ++ scale (-(1)) [(23, 1)]) = true := by
  decide +kernel

theorem cycChk24 : zeroL (wordS e8T 248 [246, 150] [(247, 1)] ++ scale (-(-1)) [(24, 1)]) = true := by
  decide +kernel

theorem cycChk25 : zeroL (wordS e8T 248 [245, 157] [(247, 1)] ++ scale (-(1)) [(25, 1)]) = true := by
  decide +kernel

theorem cycChk26 : zeroL (wordS e8T 248 [244, 164] [(247, 1)] ++ scale (-(-1)) [(26, 1)]) = true := by
  decide +kernel

theorem cycChk27 : zeroL (wordS e8T 248 [244, 165] [(247, 1)] ++ scale (-(-1)) [(27, 1)]) = true := by
  decide +kernel

theorem cycChk28 : zeroL (wordS e8T 248 [243, 171] [(247, 1)] ++ scale (-(1)) [(28, 1)]) = true := by
  decide +kernel

theorem cycChk29 : zeroL (wordS e8T 248 [243, 174] [(247, 1)] ++ scale (-(1)) [(29, 1)]) = true := by
  decide +kernel

theorem cycChk30 : zeroL (wordS e8T 248 [247, 150] [(247, 1)] ++ scale (-(1)) [(30, 1)]) = true := by
  decide +kernel

theorem cycChk31 : zeroL (wordS e8T 248 [246, 157] [(247, 1)] ++ scale (-(-1)) [(31, 1)]) = true := by
  decide +kernel

theorem cycChk32 : zeroL (wordS e8T 248 [245, 164] [(247, 1)] ++ scale (-(1)) [(32, 1)]) = true := by
  decide +kernel

theorem cycChk33 : zeroL (wordS e8T 248 [245, 165] [(247, 1)] ++ scale (-(1)) [(33, 1)]) = true := by
  decide +kernel

theorem cycChk34 : zeroL (wordS e8T 248 [244, 171] [(247, 1)] ++ scale (-(-1)) [(34, 1)]) = true := by
  decide +kernel

theorem cycChk35 : zeroL (wordS e8T 248 [244, 174] [(247, 1)] ++ scale (-(-1)) [(35, 1)]) = true := by
  decide +kernel

theorem cycChk36 : zeroL (wordS e8T 248 [243, 180] [(247, 1)] ++ scale (-(1)) [(36, 1)]) = true := by
  decide +kernel

theorem cycChk37 : zeroL (wordS e8T 248 [247, 157] [(247, 1)] ++ scale (-(1)) [(37, 1)]) = true := by
  decide +kernel

theorem cycChk38 : zeroL (wordS e8T 248 [246, 164] [(247, 1)] ++ scale (-(-1)) [(38, 1)]) = true := by
  decide +kernel

theorem cycChk39 : zeroL (wordS e8T 248 [246, 165] [(247, 1)] ++ scale (-(-1)) [(39, 1)]) = true := by
  decide +kernel

theorem cycChk40 : zeroL (wordS e8T 248 [245, 171] [(247, 1)] ++ scale (-(1)) [(40, 1)]) = true := by
  decide +kernel

theorem cycChk41 : zeroL (wordS e8T 248 [244, 178] [(247, 1)] ++ scale (-(-1)) [(41, 1)]) = true := by
  decide +kernel

theorem cycChk42 : zeroL (wordS e8T 248 [245, 174] [(247, 1)] ++ scale (-(1)) [(42, 1)]) = true := by
  decide +kernel

theorem cycChk43 : zeroL (wordS e8T 248 [244, 180] [(247, 1)] ++ scale (-(-1)) [(43, 1)]) = true := by
  decide +kernel

theorem cycChk44 : zeroL (wordS e8T 248 [247, 164] [(247, 1)] ++ scale (-(1)) [(44, 1)]) = true := by
  decide +kernel

theorem cycChk45 : zeroL (wordS e8T 248 [247, 165] [(247, 1)] ++ scale (-(1)) [(45, 1)]) = true := by
  decide +kernel

theorem cycChk46 : zeroL (wordS e8T 248 [246, 171] [(247, 1)] ++ scale (-(-1)) [(46, 1)]) = true := by
  decide +kernel

theorem cycChk47 : zeroL (wordS e8T 248 [245, 178] [(247, 1)] ++ scale (-(1)) [(47, 1)]) = true := by
  decide +kernel

theorem cycChk48 : zeroL (wordS e8T 248 [246, 174] [(247, 1)] ++ scale (-(-1)) [(48, 1)]) = true := by
  decide +kernel

theorem cycChk49 : zeroL (wordS e8T 248 [245, 180] [(247, 1)] ++ scale (-(1)) [(49, 1)]) = true := by
  decide +kernel

theorem cycChk50 : zeroL (wordS e8T 248 [244, 186] [(247, 1)] ++ scale (-(-1)) [(50, 1)]) = true := by
  decide +kernel

theorem cycChk51 : zeroL (wordS e8T 248 [247, 171] [(247, 1)] ++ scale (-(1)) [(51, 1)]) = true := by
  decide +kernel

theorem cycChk52 : zeroL (wordS e8T 248 [246, 178] [(247, 1)] ++ scale (-(-1)) [(52, 1)]) = true := by
  decide +kernel

theorem cycChk53 : zeroL (wordS e8T 248 [245, 184] [(247, 1)] ++ scale (-(1)) [(53, 1)]) = true := by
  decide +kernel

theorem cycChk54 : zeroL (wordS e8T 248 [247, 174] [(247, 1)] ++ scale (-(1)) [(54, 1)]) = true := by
  decide +kernel

theorem cycChk55 : zeroL (wordS e8T 248 [246, 180] [(247, 1)] ++ scale (-(-1)) [(55, 1)]) = true := by
  decide +kernel

theorem cycChk56 : zeroL (wordS e8T 248 [245, 186] [(247, 1)] ++ scale (-(1)) [(56, 1)]) = true := by
  decide +kernel

theorem cycChk57 : zeroL (wordS e8T 248 [244, 193] [(247, 1)] ++ scale (-(-1)) [(57, 1)]) = true := by
  decide +kernel

theorem cycChk58 : zeroL (wordS e8T 248 [247, 178] [(247, 1)] ++ scale (-(1)) [(58, 1)]) = true := by
  decide +kernel

theorem cycChk59 : zeroL (wordS e8T 248 [246, 184] [(247, 1)] ++ scale (-(-1)) [(59, 1)]) = true := by
  decide +kernel

theorem cycChk60 : zeroL (wordS e8T 248 [247, 180] [(247, 1)] ++ scale (-(1)) [(60, 1)]) = true := by
  decide +kernel

theorem cycChk61 : zeroL (wordS e8T 248 [246, 186] [(247, 1)] ++ scale (-(-1)) [(61, 1)]) = true := by
  decide +kernel

theorem cycChk62 : zeroL (wordS e8T 248 [245, 191] [(247, 1)] ++ scale (-(1)) [(62, 1)]) = true := by
  decide +kernel

theorem cycChk63 : zeroL (wordS e8T 248 [245, 193] [(247, 1)] ++ scale (-(1)) [(63, 1)]) = true := by
  decide +kernel

theorem cycChk64 : zeroL (wordS e8T 248 [247, 184] [(247, 1)] ++ scale (-(1)) [(64, 1)]) = true := by
  decide +kernel

theorem cycChk65 : zeroL (wordS e8T 248 [246, 190] [(247, 1)] ++ scale (-(-1)) [(65, 1)]) = true := by
  decide +kernel

theorem cycChk66 : zeroL (wordS e8T 248 [247, 186] [(247, 1)] ++ scale (-(1)) [(66, 1)]) = true := by
  decide +kernel

theorem cycChk67 : zeroL (wordS e8T 248 [246, 191] [(247, 1)] ++ scale (-(-1)) [(67, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
