/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `e8T` agrees with `E8Lie.sL`, rows `0..63`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem rowLink0 : (List.range' 0 4).all rowLinkOK = true := by decide +kernel

theorem rowLink1 : (List.range' 4 4).all rowLinkOK = true := by decide +kernel

theorem rowLink2 : (List.range' 8 4).all rowLinkOK = true := by decide +kernel

theorem rowLink3 : (List.range' 12 4).all rowLinkOK = true := by decide +kernel

theorem rowLink4 : (List.range' 16 4).all rowLinkOK = true := by decide +kernel

theorem rowLink5 : (List.range' 20 4).all rowLinkOK = true := by decide +kernel

theorem rowLink6 : (List.range' 24 4).all rowLinkOK = true := by decide +kernel

theorem rowLink7 : (List.range' 28 4).all rowLinkOK = true := by decide +kernel

theorem rowLink8 : (List.range' 32 4).all rowLinkOK = true := by decide +kernel

theorem rowLink9 : (List.range' 36 4).all rowLinkOK = true := by decide +kernel

theorem rowLink10 : (List.range' 40 4).all rowLinkOK = true := by decide +kernel

theorem rowLink11 : (List.range' 44 4).all rowLinkOK = true := by decide +kernel

theorem rowLink12 : (List.range' 48 4).all rowLinkOK = true := by decide +kernel

theorem rowLink13 : (List.range' 52 4).all rowLinkOK = true := by decide +kernel

theorem rowLink14 : (List.range' 56 4).all rowLinkOK = true := by decide +kernel

theorem rowLink15 : (List.range' 60 4).all rowLinkOK = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
