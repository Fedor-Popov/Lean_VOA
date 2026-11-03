/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `68..127` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk68 : zeroL (wordS e8T 248 [246, 193] [(247, 1)] ++ scale (-(-1)) [(68, 1)]) = true := by
  decide +kernel

theorem cycChk69 : zeroL (wordS e8T 248 [245, 198] [(247, 1)] ++ scale (-(1)) [(69, 1)]) = true := by
  decide +kernel

theorem cycChk70 : zeroL (wordS e8T 248 [247, 190] [(247, 1)] ++ scale (-(1)) [(70, 1)]) = true := by
  decide +kernel

theorem cycChk71 : zeroL (wordS e8T 248 [247, 191] [(247, 1)] ++ scale (-(1)) [(71, 1)]) = true := by
  decide +kernel

theorem cycChk72 : zeroL (wordS e8T 248 [246, 197] [(247, 1)] ++ scale (-(-1)) [(72, 1)]) = true := by
  decide +kernel

theorem cycChk73 : zeroL (wordS e8T 248 [247, 193] [(247, 1)] ++ scale (-(1)) [(73, 1)]) = true := by
  decide +kernel

theorem cycChk74 : zeroL (wordS e8T 248 [246, 198] [(247, 1)] ++ scale (-(-1)) [(74, 1)]) = true := by
  decide +kernel

theorem cycChk75 : zeroL (wordS e8T 248 [245, 204] [(247, 1)] ++ scale (-(1)) [(75, 1)]) = true := by
  decide +kernel

theorem cycChk76 : zeroL (wordS e8T 248 [247, 196] [(247, 1)] ++ scale (-(1)) [(76, 1)]) = true := by
  decide +kernel

theorem cycChk77 : zeroL (wordS e8T 248 [247, 197] [(247, 1)] ++ scale (-(1)) [(77, 1)]) = true := by
  decide +kernel

theorem cycChk78 : zeroL (wordS e8T 248 [247, 198] [(247, 1)] ++ scale (-(1)) [(78, 1)]) = true := by
  decide +kernel

theorem cycChk79 : zeroL (wordS e8T 248 [246, 203] [(247, 1)] ++ scale (-(-1)) [(79, 1)]) = true := by
  decide +kernel

theorem cycChk80 : zeroL (wordS e8T 248 [246, 204] [(247, 1)] ++ scale (-(-1)) [(80, 1)]) = true := by
  decide +kernel

theorem cycChk81 : zeroL (wordS e8T 248 [245, 210] [(247, 1)] ++ scale (-(1)) [(81, 1)]) = true := by
  decide +kernel

theorem cycChk82 : zeroL (wordS e8T 248 [247, 202] [(247, 1)] ++ scale (-(1)) [(82, 1)]) = true := by
  decide +kernel

theorem cycChk83 : zeroL (wordS e8T 248 [247, 203] [(247, 1)] ++ scale (-(1)) [(83, 1)]) = true := by
  decide +kernel

theorem cycChk84 : zeroL (wordS e8T 248 [247, 204] [(247, 1)] ++ scale (-(1)) [(84, 1)]) = true := by
  decide +kernel

theorem cycChk85 : zeroL (wordS e8T 248 [246, 208] [(247, 1)] ++ scale (-(-1)) [(85, 1)]) = true := by
  decide +kernel

theorem cycChk86 : zeroL (wordS e8T 248 [246, 210] [(247, 1)] ++ scale (-(-1)) [(86, 1)]) = true := by
  decide +kernel

theorem cycChk87 : zeroL (wordS e8T 248 [247, 207] [(247, 1)] ++ scale (-(1)) [(87, 1)]) = true := by
  decide +kernel

theorem cycChk88 : zeroL (wordS e8T 248 [247, 208] [(247, 1)] ++ scale (-(1)) [(88, 1)]) = true := by
  decide +kernel

theorem cycChk89 : zeroL (wordS e8T 248 [246, 213] [(247, 1)] ++ scale (-(-1)) [(89, 1)]) = true := by
  decide +kernel

theorem cycChk90 : zeroL (wordS e8T 248 [247, 210] [(247, 1)] ++ scale (-(1)) [(90, 1)]) = true := by
  decide +kernel

theorem cycChk91 : zeroL (wordS e8T 248 [246, 214] [(247, 1)] ++ scale (-(-1)) [(91, 1)]) = true := by
  decide +kernel

theorem cycChk92 : zeroL (wordS e8T 248 [247, 212] [(247, 1)] ++ scale (-(1)) [(92, 1)]) = true := by
  decide +kernel

theorem cycChk93 : zeroL (wordS e8T 248 [247, 213] [(247, 1)] ++ scale (-(1)) [(93, 1)]) = true := by
  decide +kernel

theorem cycChk94 : zeroL (wordS e8T 248 [247, 214] [(247, 1)] ++ scale (-(1)) [(94, 1)]) = true := by
  decide +kernel

theorem cycChk95 : zeroL (wordS e8T 248 [246, 218] [(247, 1)] ++ scale (-(-1)) [(95, 1)]) = true := by
  decide +kernel

theorem cycChk96 : zeroL (wordS e8T 248 [247, 216] [(247, 1)] ++ scale (-(1)) [(96, 1)]) = true := by
  decide +kernel

theorem cycChk97 : zeroL (wordS e8T 248 [247, 217] [(247, 1)] ++ scale (-(1)) [(97, 1)]) = true := by
  decide +kernel

theorem cycChk98 : zeroL (wordS e8T 248 [247, 218] [(247, 1)] ++ scale (-(1)) [(98, 1)]) = true := by
  decide +kernel

theorem cycChk99 : zeroL (wordS e8T 248 [246, 222] [(247, 1)] ++ scale (-(-1)) [(99, 1)]) = true := by
  decide +kernel

theorem cycChk100 : zeroL (wordS e8T 248 [247, 220] [(247, 1)] ++ scale (-(1)) [(100, 1)]) = true := by
  decide +kernel

theorem cycChk101 : zeroL (wordS e8T 248 [247, 221] [(247, 1)] ++ scale (-(1)) [(101, 1)]) = true := by
  decide +kernel

theorem cycChk102 : zeroL (wordS e8T 248 [247, 222] [(247, 1)] ++ scale (-(1)) [(102, 1)]) = true := by
  decide +kernel

theorem cycChk103 : zeroL (wordS e8T 248 [246, 226] [(247, 1)] ++ scale (-(-1)) [(103, 1)]) = true := by
  decide +kernel

theorem cycChk104 : zeroL (wordS e8T 248 [247, 224] [(247, 1)] ++ scale (-(1)) [(104, 1)]) = true := by
  decide +kernel

theorem cycChk105 : zeroL (wordS e8T 248 [247, 225] [(247, 1)] ++ scale (-(1)) [(105, 1)]) = true := by
  decide +kernel

theorem cycChk106 : zeroL (wordS e8T 248 [247, 226] [(247, 1)] ++ scale (-(1)) [(106, 1)]) = true := by
  decide +kernel

theorem cycChk107 : zeroL (wordS e8T 248 [246, 230] [(247, 1)] ++ scale (-(-1)) [(107, 1)]) = true := by
  decide +kernel

theorem cycChk108 : zeroL (wordS e8T 248 [247, 228] [(247, 1)] ++ scale (-(1)) [(108, 1)]) = true := by
  decide +kernel

theorem cycChk109 : zeroL (wordS e8T 248 [247, 229] [(247, 1)] ++ scale (-(1)) [(109, 1)]) = true := by
  decide +kernel

theorem cycChk110 : zeroL (wordS e8T 248 [247, 230] [(247, 1)] ++ scale (-(1)) [(110, 1)]) = true := by
  decide +kernel

theorem cycChk111 : zeroL (wordS e8T 248 [247, 231] [(247, 1)] ++ scale (-(1)) [(111, 1)]) = true := by
  decide +kernel

theorem cycChk112 : zeroL (wordS e8T 248 [247, 232] [(247, 1)] ++ scale (-(1)) [(112, 1)]) = true := by
  decide +kernel

theorem cycChk113 : zeroL (wordS e8T 248 [247, 233] [(247, 1)] ++ scale (-(1)) [(113, 1)]) = true := by
  decide +kernel

theorem cycChk114 : zeroL (wordS e8T 248 [247, 234] [(247, 1)] ++ scale (-(1)) [(114, 1)]) = true := by
  decide +kernel

theorem cycChk115 : zeroL (wordS e8T 248 [247, 235] [(247, 1)] ++ scale (-(1)) [(115, 1)]) = true := by
  decide +kernel

theorem cycChk116 : zeroL (wordS e8T 248 [247, 236] [(247, 1)] ++ scale (-(1)) [(116, 1)]) = true := by
  decide +kernel

theorem cycChk117 : zeroL (wordS e8T 248 [247, 237] [(247, 1)] ++ scale (-(1)) [(117, 1)]) = true := by
  decide +kernel

theorem cycChk118 : zeroL (wordS e8T 248 [247, 238] [(247, 1)] ++ scale (-(1)) [(118, 1)]) = true := by
  decide +kernel

theorem cycChk119 : zeroL (wordS e8T 248 [247, 239] [(247, 1)] ++ scale (-(1)) [(119, 1)]) = true := by
  decide +kernel

theorem cycChk120 : zeroL (wordS e8T 248 [247, 240] [(247, 1)] ++ scale (-(1)) [(120, 1)]) = true := by
  decide +kernel

theorem cycChk121 : zeroL (wordS e8T 248 [247, 241] [(247, 1)] ++ scale (-(1)) [(121, 1)]) = true := by
  decide +kernel

theorem cycChk122 : zeroL (wordS e8T 248 [247, 242] [(247, 1)] ++ scale (-(1)) [(122, 1)]) = true := by
  decide +kernel

theorem cycChk123 : zeroL (wordS e8T 248 [247, 243] [(247, 1)] ++ scale (-(1)) [(123, 1)]) = true := by
  decide +kernel

theorem cycChk124 : zeroL (wordS e8T 248 [247, 244] [(247, 1)] ++ scale (-(1)) [(124, 1)]) = true := by
  decide +kernel

theorem cycChk125 : zeroL (wordS e8T 248 [247, 245] [(247, 1)] ++ scale (-(1)) [(125, 1)]) = true := by
  decide +kernel

theorem cycChk126 : zeroL (wordS e8T 248 [247, 246] [(247, 1)] ++ scale (-(1)) [(126, 1)]) = true := by
  decide +kernel

theorem cycChk127 : zeroL (wordS e8T 248 [247, 247] [(247, 1)] ++ scale (-(2)) [(127, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
