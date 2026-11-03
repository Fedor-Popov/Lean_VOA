/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` coadjoint cyclicity: Boolean word checks `128..187` (depth 2 from `δ_{247}`, light imports)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6SectorSparse

set_option linter.style.longLine false

theorem cycChk128 : zeroL (wordS e8T 248 [246] [(247, 1)] ++ scale (-(1)) [(128, 1)]) = true := by
  decide +kernel

theorem cycChk129 : zeroL (wordS e8T 248 [245, 128] [(247, 1)] ++ scale (-(-1)) [(129, 1)]) = true := by
  decide +kernel

theorem cycChk130 : zeroL (wordS e8T 248 [244, 136] [(247, 1)] ++ scale (-(-1)) [(130, 1)]) = true := by
  decide +kernel

theorem cycChk131 : zeroL (wordS e8T 248 [243, 143] [(247, 1)] ++ scale (-(1)) [(131, 1)]) = true := by
  decide +kernel

theorem cycChk132 : zeroL (wordS e8T 248 [242, 150] [(247, 1)] ++ scale (-(-1)) [(132, 1)]) = true := by
  decide +kernel

theorem cycChk133 : zeroL (wordS e8T 248 [241, 157] [(247, 1)] ++ scale (-(-1)) [(133, 1)]) = true := by
  decide +kernel

theorem cycChk134 : zeroL (wordS e8T 248 [240, 157] [(247, 1)] ++ scale (-(1)) [(134, 1)]) = true := by
  decide +kernel

theorem cycChk135 : zeroL (wordS e8T 248 [238, 164] [(247, 1)] ++ scale (-(-1)) [(135, 1)]) = true := by
  decide +kernel

theorem cycChk136 : zeroL (wordS e8T 248 [245] [(247, 1)] ++ scale (-(1)) [(136, 1)]) = true := by
  decide +kernel

theorem cycChk137 : zeroL (wordS e8T 248 [244, 128] [(247, 1)] ++ scale (-(-1)) [(137, 1)]) = true := by
  decide +kernel

theorem cycChk138 : zeroL (wordS e8T 248 [243, 136] [(247, 1)] ++ scale (-(-1)) [(138, 1)]) = true := by
  decide +kernel

theorem cycChk139 : zeroL (wordS e8T 248 [242, 143] [(247, 1)] ++ scale (-(1)) [(139, 1)]) = true := by
  decide +kernel

theorem cycChk140 : zeroL (wordS e8T 248 [241, 150] [(247, 1)] ++ scale (-(1)) [(140, 1)]) = true := by
  decide +kernel

theorem cycChk141 : zeroL (wordS e8T 248 [240, 150] [(247, 1)] ++ scale (-(-1)) [(141, 1)]) = true := by
  decide +kernel

theorem cycChk142 : zeroL (wordS e8T 248 [238, 157] [(247, 1)] ++ scale (-(1)) [(142, 1)]) = true := by
  decide +kernel

theorem cycChk143 : zeroL (wordS e8T 248 [244] [(247, 1)] ++ scale (-(-1)) [(143, 1)]) = true := by
  decide +kernel

theorem cycChk144 : zeroL (wordS e8T 248 [243, 128] [(247, 1)] ++ scale (-(1)) [(144, 1)]) = true := by
  decide +kernel

theorem cycChk145 : zeroL (wordS e8T 248 [242, 136] [(247, 1)] ++ scale (-(1)) [(145, 1)]) = true := by
  decide +kernel

theorem cycChk146 : zeroL (wordS e8T 248 [241, 143] [(247, 1)] ++ scale (-(1)) [(146, 1)]) = true := by
  decide +kernel

theorem cycChk147 : zeroL (wordS e8T 248 [240, 143] [(247, 1)] ++ scale (-(-1)) [(147, 1)]) = true := by
  decide +kernel

theorem cycChk148 : zeroL (wordS e8T 248 [239, 150] [(247, 1)] ++ scale (-(-1)) [(148, 1)]) = true := by
  decide +kernel

theorem cycChk149 : zeroL (wordS e8T 248 [238, 150] [(247, 1)] ++ scale (-(1)) [(149, 1)]) = true := by
  decide +kernel

theorem cycChk150 : zeroL (wordS e8T 248 [243] [(247, 1)] ++ scale (-(1)) [(150, 1)]) = true := by
  decide +kernel

theorem cycChk151 : zeroL (wordS e8T 248 [242, 128] [(247, 1)] ++ scale (-(-1)) [(151, 1)]) = true := by
  decide +kernel

theorem cycChk152 : zeroL (wordS e8T 248 [241, 136] [(247, 1)] ++ scale (-(1)) [(152, 1)]) = true := by
  decide +kernel

theorem cycChk153 : zeroL (wordS e8T 248 [240, 136] [(247, 1)] ++ scale (-(-1)) [(153, 1)]) = true := by
  decide +kernel

theorem cycChk154 : zeroL (wordS e8T 248 [239, 143] [(247, 1)] ++ scale (-(-1)) [(154, 1)]) = true := by
  decide +kernel

theorem cycChk155 : zeroL (wordS e8T 248 [238, 143] [(247, 1)] ++ scale (-(1)) [(155, 1)]) = true := by
  decide +kernel

theorem cycChk156 : zeroL (wordS e8T 248 [236, 150] [(247, 1)] ++ scale (-(-1)) [(156, 1)]) = true := by
  decide +kernel

theorem cycChk157 : zeroL (wordS e8T 248 [242] [(247, 1)] ++ scale (-(-1)) [(157, 1)]) = true := by
  decide +kernel

theorem cycChk158 : zeroL (wordS e8T 248 [241, 128] [(247, 1)] ++ scale (-(-1)) [(158, 1)]) = true := by
  decide +kernel

theorem cycChk159 : zeroL (wordS e8T 248 [240, 128] [(247, 1)] ++ scale (-(1)) [(159, 1)]) = true := by
  decide +kernel

theorem cycChk160 : zeroL (wordS e8T 248 [239, 136] [(247, 1)] ++ scale (-(-1)) [(160, 1)]) = true := by
  decide +kernel

theorem cycChk161 : zeroL (wordS e8T 248 [237, 143] [(247, 1)] ++ scale (-(1)) [(161, 1)]) = true := by
  decide +kernel

theorem cycChk162 : zeroL (wordS e8T 248 [238, 136] [(247, 1)] ++ scale (-(1)) [(162, 1)]) = true := by
  decide +kernel

theorem cycChk163 : zeroL (wordS e8T 248 [236, 143] [(247, 1)] ++ scale (-(-1)) [(163, 1)]) = true := by
  decide +kernel

theorem cycChk164 : zeroL (wordS e8T 248 [241] [(247, 1)] ++ scale (-(-1)) [(164, 1)]) = true := by
  decide +kernel

theorem cycChk165 : zeroL (wordS e8T 248 [240] [(247, 1)] ++ scale (-(1)) [(165, 1)]) = true := by
  decide +kernel

theorem cycChk166 : zeroL (wordS e8T 248 [239, 128] [(247, 1)] ++ scale (-(1)) [(166, 1)]) = true := by
  decide +kernel

theorem cycChk167 : zeroL (wordS e8T 248 [237, 136] [(247, 1)] ++ scale (-(1)) [(167, 1)]) = true := by
  decide +kernel

theorem cycChk168 : zeroL (wordS e8T 248 [238, 128] [(247, 1)] ++ scale (-(-1)) [(168, 1)]) = true := by
  decide +kernel

theorem cycChk169 : zeroL (wordS e8T 248 [236, 136] [(247, 1)] ++ scale (-(-1)) [(169, 1)]) = true := by
  decide +kernel

theorem cycChk170 : zeroL (wordS e8T 248 [234, 143] [(247, 1)] ++ scale (-(1)) [(170, 1)]) = true := by
  decide +kernel

theorem cycChk171 : zeroL (wordS e8T 248 [239] [(247, 1)] ++ scale (-(1)) [(171, 1)]) = true := by
  decide +kernel

theorem cycChk172 : zeroL (wordS e8T 248 [237, 128] [(247, 1)] ++ scale (-(-1)) [(172, 1)]) = true := by
  decide +kernel

theorem cycChk173 : zeroL (wordS e8T 248 [235, 136] [(247, 1)] ++ scale (-(-1)) [(173, 1)]) = true := by
  decide +kernel

theorem cycChk174 : zeroL (wordS e8T 248 [238] [(247, 1)] ++ scale (-(-1)) [(174, 1)]) = true := by
  decide +kernel

theorem cycChk175 : zeroL (wordS e8T 248 [236, 128] [(247, 1)] ++ scale (-(1)) [(175, 1)]) = true := by
  decide +kernel

theorem cycChk176 : zeroL (wordS e8T 248 [234, 136] [(247, 1)] ++ scale (-(1)) [(176, 1)]) = true := by
  decide +kernel

theorem cycChk177 : zeroL (wordS e8T 248 [231, 143] [(247, 1)] ++ scale (-(1)) [(177, 1)]) = true := by
  decide +kernel

theorem cycChk178 : zeroL (wordS e8T 248 [237] [(247, 1)] ++ scale (-(-1)) [(178, 1)]) = true := by
  decide +kernel

theorem cycChk179 : zeroL (wordS e8T 248 [235, 128] [(247, 1)] ++ scale (-(1)) [(179, 1)]) = true := by
  decide +kernel

theorem cycChk180 : zeroL (wordS e8T 248 [236] [(247, 1)] ++ scale (-(1)) [(180, 1)]) = true := by
  decide +kernel

theorem cycChk181 : zeroL (wordS e8T 248 [234, 128] [(247, 1)] ++ scale (-(-1)) [(181, 1)]) = true := by
  decide +kernel

theorem cycChk182 : zeroL (wordS e8T 248 [232, 136] [(247, 1)] ++ scale (-(-1)) [(182, 1)]) = true := by
  decide +kernel

theorem cycChk183 : zeroL (wordS e8T 248 [231, 136] [(247, 1)] ++ scale (-(1)) [(183, 1)]) = true := by
  decide +kernel

theorem cycChk184 : zeroL (wordS e8T 248 [235] [(247, 1)] ++ scale (-(1)) [(184, 1)]) = true := by
  decide +kernel

theorem cycChk185 : zeroL (wordS e8T 248 [233, 128] [(247, 1)] ++ scale (-(-1)) [(185, 1)]) = true := by
  decide +kernel

theorem cycChk186 : zeroL (wordS e8T 248 [234] [(247, 1)] ++ scale (-(-1)) [(186, 1)]) = true := by
  decide +kernel

theorem cycChk187 : zeroL (wordS e8T 248 [232, 128] [(247, 1)] ++ scale (-(1)) [(187, 1)]) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
