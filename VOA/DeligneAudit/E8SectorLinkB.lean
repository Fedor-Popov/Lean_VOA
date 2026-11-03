/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `e8T` agrees with `E8Lie.sL`, rows `64..127`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem rowLink16 : (List.range' 64 4).all rowLinkOK = true := by decide +kernel

theorem rowLink17 : (List.range' 68 4).all rowLinkOK = true := by decide +kernel

theorem rowLink18 : (List.range' 72 4).all rowLinkOK = true := by decide +kernel

theorem rowLink19 : (List.range' 76 4).all rowLinkOK = true := by decide +kernel

theorem rowLink20 : (List.range' 80 4).all rowLinkOK = true := by decide +kernel

theorem rowLink21 : (List.range' 84 4).all rowLinkOK = true := by decide +kernel

theorem rowLink22 : (List.range' 88 4).all rowLinkOK = true := by decide +kernel

theorem rowLink23 : (List.range' 92 4).all rowLinkOK = true := by decide +kernel

theorem rowLink24 : (List.range' 96 4).all rowLinkOK = true := by decide +kernel

theorem rowLink25 : (List.range' 100 4).all rowLinkOK = true := by decide +kernel

theorem rowLink26 : (List.range' 104 4).all rowLinkOK = true := by decide +kernel

theorem rowLink27 : (List.range' 108 4).all rowLinkOK = true := by decide +kernel

theorem rowLink28 : (List.range' 112 4).all rowLinkOK = true := by decide +kernel

theorem rowLink29 : (List.range' 116 4).all rowLinkOK = true := by decide +kernel

theorem rowLink30 : (List.range' 120 4).all rowLinkOK = true := by decide +kernel

theorem rowLink31 : (List.range' 124 4).all rowLinkOK = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
