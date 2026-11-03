/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `188..247` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk188 : zeroL (wordS e8T 248 [231, 128] [(247, 1)] ++ scale (-(-1)) [(188, 1)]) = true := by
  decide +kernel

theorem cycChk189 : zeroL (wordS e8T 248 [228, 136] [(247, 1)] ++ scale (-(-1)) [(189, 1)]) = true := by
  decide +kernel

theorem cycChk190 : zeroL (wordS e8T 248 [233] [(247, 1)] ++ scale (-(-1)) [(190, 1)]) = true := by
  decide +kernel

theorem cycChk191 : zeroL (wordS e8T 248 [232] [(247, 1)] ++ scale (-(1)) [(191, 1)]) = true := by
  decide +kernel

theorem cycChk192 : zeroL (wordS e8T 248 [229, 128] [(247, 1)] ++ scale (-(-1)) [(192, 1)]) = true := by
  decide +kernel

theorem cycChk193 : zeroL (wordS e8T 248 [231] [(247, 1)] ++ scale (-(-1)) [(193, 1)]) = true := by
  decide +kernel

theorem cycChk194 : zeroL (wordS e8T 248 [228, 128] [(247, 1)] ++ scale (-(1)) [(194, 1)]) = true := by
  decide +kernel

theorem cycChk195 : zeroL (wordS e8T 248 [224, 136] [(247, 1)] ++ scale (-(1)) [(195, 1)]) = true := by
  decide +kernel

theorem cycChk196 : zeroL (wordS e8T 248 [230] [(247, 1)] ++ scale (-(1)) [(196, 1)]) = true := by
  decide +kernel

theorem cycChk197 : zeroL (wordS e8T 248 [229] [(247, 1)] ++ scale (-(-1)) [(197, 1)]) = true := by
  decide +kernel

theorem cycChk198 : zeroL (wordS e8T 248 [228] [(247, 1)] ++ scale (-(1)) [(198, 1)]) = true := by
  decide +kernel

theorem cycChk199 : zeroL (wordS e8T 248 [225, 128] [(247, 1)] ++ scale (-(-1)) [(199, 1)]) = true := by
  decide +kernel

theorem cycChk200 : zeroL (wordS e8T 248 [224, 128] [(247, 1)] ++ scale (-(-1)) [(200, 1)]) = true := by
  decide +kernel

theorem cycChk201 : zeroL (wordS e8T 248 [220, 136] [(247, 1)] ++ scale (-(-1)) [(201, 1)]) = true := by
  decide +kernel

theorem cycChk202 : zeroL (wordS e8T 248 [226] [(247, 1)] ++ scale (-(1)) [(202, 1)]) = true := by
  decide +kernel

theorem cycChk203 : zeroL (wordS e8T 248 [225] [(247, 1)] ++ scale (-(-1)) [(203, 1)]) = true := by
  decide +kernel

theorem cycChk204 : zeroL (wordS e8T 248 [224] [(247, 1)] ++ scale (-(-1)) [(204, 1)]) = true := by
  decide +kernel

theorem cycChk205 : zeroL (wordS e8T 248 [221, 128] [(247, 1)] ++ scale (-(1)) [(205, 1)]) = true := by
  decide +kernel

theorem cycChk206 : zeroL (wordS e8T 248 [220, 128] [(247, 1)] ++ scale (-(1)) [(206, 1)]) = true := by
  decide +kernel

theorem cycChk207 : zeroL (wordS e8T 248 [222] [(247, 1)] ++ scale (-(1)) [(207, 1)]) = true := by
  decide +kernel

theorem cycChk208 : zeroL (wordS e8T 248 [221] [(247, 1)] ++ scale (-(1)) [(208, 1)]) = true := by
  decide +kernel

theorem cycChk209 : zeroL (wordS e8T 248 [217, 128] [(247, 1)] ++ scale (-(-1)) [(209, 1)]) = true := by
  decide +kernel

theorem cycChk210 : zeroL (wordS e8T 248 [220] [(247, 1)] ++ scale (-(1)) [(210, 1)]) = true := by
  decide +kernel

theorem cycChk211 : zeroL (wordS e8T 248 [216, 128] [(247, 1)] ++ scale (-(-1)) [(211, 1)]) = true := by
  decide +kernel

theorem cycChk212 : zeroL (wordS e8T 248 [218] [(247, 1)] ++ scale (-(-1)) [(212, 1)]) = true := by
  decide +kernel

theorem cycChk213 : zeroL (wordS e8T 248 [217] [(247, 1)] ++ scale (-(-1)) [(213, 1)]) = true := by
  decide +kernel

theorem cycChk214 : zeroL (wordS e8T 248 [216] [(247, 1)] ++ scale (-(-1)) [(214, 1)]) = true := by
  decide +kernel

theorem cycChk215 : zeroL (wordS e8T 248 [212, 128] [(247, 1)] ++ scale (-(1)) [(215, 1)]) = true := by
  decide +kernel

theorem cycChk216 : zeroL (wordS e8T 248 [214] [(247, 1)] ++ scale (-(1)) [(216, 1)]) = true := by
  decide +kernel

theorem cycChk217 : zeroL (wordS e8T 248 [213] [(247, 1)] ++ scale (-(1)) [(217, 1)]) = true := by
  decide +kernel

theorem cycChk218 : zeroL (wordS e8T 248 [212] [(247, 1)] ++ scale (-(1)) [(218, 1)]) = true := by
  decide +kernel

theorem cycChk219 : zeroL (wordS e8T 248 [207, 128] [(247, 1)] ++ scale (-(-1)) [(219, 1)]) = true := by
  decide +kernel

theorem cycChk220 : zeroL (wordS e8T 248 [210] [(247, 1)] ++ scale (-(-1)) [(220, 1)]) = true := by
  decide +kernel

theorem cycChk221 : zeroL (wordS e8T 248 [208] [(247, 1)] ++ scale (-(-1)) [(221, 1)]) = true := by
  decide +kernel

theorem cycChk222 : zeroL (wordS e8T 248 [207] [(247, 1)] ++ scale (-(-1)) [(222, 1)]) = true := by
  decide +kernel

theorem cycChk223 : zeroL (wordS e8T 248 [202, 128] [(247, 1)] ++ scale (-(-1)) [(223, 1)]) = true := by
  decide +kernel

theorem cycChk224 : zeroL (wordS e8T 248 [204] [(247, 1)] ++ scale (-(1)) [(224, 1)]) = true := by
  decide +kernel

theorem cycChk225 : zeroL (wordS e8T 248 [203] [(247, 1)] ++ scale (-(1)) [(225, 1)]) = true := by
  decide +kernel

theorem cycChk226 : zeroL (wordS e8T 248 [202] [(247, 1)] ++ scale (-(-1)) [(226, 1)]) = true := by
  decide +kernel

theorem cycChk227 : zeroL (wordS e8T 248 [196, 128] [(247, 1)] ++ scale (-(-1)) [(227, 1)]) = true := by
  decide +kernel

theorem cycChk228 : zeroL (wordS e8T 248 [198] [(247, 1)] ++ scale (-(-1)) [(228, 1)]) = true := by
  decide +kernel

theorem cycChk229 : zeroL (wordS e8T 248 [197] [(247, 1)] ++ scale (-(1)) [(229, 1)]) = true := by
  decide +kernel

theorem cycChk230 : zeroL (wordS e8T 248 [196] [(247, 1)] ++ scale (-(-1)) [(230, 1)]) = true := by
  decide +kernel

theorem cycChk231 : zeroL (wordS e8T 248 [193] [(247, 1)] ++ scale (-(1)) [(231, 1)]) = true := by
  decide +kernel

theorem cycChk232 : zeroL (wordS e8T 248 [191] [(247, 1)] ++ scale (-(-1)) [(232, 1)]) = true := by
  decide +kernel

theorem cycChk233 : zeroL (wordS e8T 248 [190] [(247, 1)] ++ scale (-(1)) [(233, 1)]) = true := by
  decide +kernel

theorem cycChk234 : zeroL (wordS e8T 248 [186] [(247, 1)] ++ scale (-(1)) [(234, 1)]) = true := by
  decide +kernel

theorem cycChk235 : zeroL (wordS e8T 248 [184] [(247, 1)] ++ scale (-(-1)) [(235, 1)]) = true := by
  decide +kernel

theorem cycChk236 : zeroL (wordS e8T 248 [180] [(247, 1)] ++ scale (-(-1)) [(236, 1)]) = true := by
  decide +kernel

theorem cycChk237 : zeroL (wordS e8T 248 [178] [(247, 1)] ++ scale (-(1)) [(237, 1)]) = true := by
  decide +kernel

theorem cycChk238 : zeroL (wordS e8T 248 [174] [(247, 1)] ++ scale (-(1)) [(238, 1)]) = true := by
  decide +kernel

theorem cycChk239 : zeroL (wordS e8T 248 [171] [(247, 1)] ++ scale (-(-1)) [(239, 1)]) = true := by
  decide +kernel

theorem cycChk240 : zeroL (wordS e8T 248 [165] [(247, 1)] ++ scale (-(-1)) [(240, 1)]) = true := by
  decide +kernel

theorem cycChk241 : zeroL (wordS e8T 248 [164] [(247, 1)] ++ scale (-(1)) [(241, 1)]) = true := by
  decide +kernel

theorem cycChk242 : zeroL (wordS e8T 248 [157] [(247, 1)] ++ scale (-(1)) [(242, 1)]) = true := by
  decide +kernel

theorem cycChk243 : zeroL (wordS e8T 248 [150] [(247, 1)] ++ scale (-(-1)) [(243, 1)]) = true := by
  decide +kernel

theorem cycChk244 : zeroL (wordS e8T 248 [143] [(247, 1)] ++ scale (-(1)) [(244, 1)]) = true := by
  decide +kernel

theorem cycChk245 : zeroL (wordS e8T 248 [136] [(247, 1)] ++ scale (-(-1)) [(245, 1)]) = true := by
  decide +kernel

theorem cycChk246 : zeroL (wordS e8T 248 [128] [(247, 1)] ++ scale (-(-1)) [(246, 1)]) = true := by
  decide +kernel

theorem cycChk247 : zeroL (wordS e8T 248 [7] [(247, 1)] ++ scale (-(1)) [(247, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
