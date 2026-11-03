/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `e8T` agrees with `E8Lie.sL`, rows `192..247`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem rowLink48 : (List.range' 192 4).all rowLinkOK = true := by decide +kernel

theorem rowLink49 : (List.range' 196 4).all rowLinkOK = true := by decide +kernel

theorem rowLink50 : (List.range' 200 4).all rowLinkOK = true := by decide +kernel

theorem rowLink51 : (List.range' 204 4).all rowLinkOK = true := by decide +kernel

theorem rowLink52 : (List.range' 208 4).all rowLinkOK = true := by decide +kernel

theorem rowLink53 : (List.range' 212 4).all rowLinkOK = true := by decide +kernel

theorem rowLink54 : (List.range' 216 4).all rowLinkOK = true := by decide +kernel

theorem rowLink55 : (List.range' 220 4).all rowLinkOK = true := by decide +kernel

theorem rowLink56 : (List.range' 224 4).all rowLinkOK = true := by decide +kernel

theorem rowLink57 : (List.range' 228 4).all rowLinkOK = true := by decide +kernel

theorem rowLink58 : (List.range' 232 4).all rowLinkOK = true := by decide +kernel

theorem rowLink59 : (List.range' 236 4).all rowLinkOK = true := by decide +kernel

theorem rowLink60 : (List.range' 240 4).all rowLinkOK = true := by decide +kernel

theorem rowLink61 : (List.range' 244 4).all rowLinkOK = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
