/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `e8T` agrees with `E8Lie.sL`, rows `128..191`
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem rowLink32 : (List.range' 128 4).all rowLinkOK = true := by decide +kernel

theorem rowLink33 : (List.range' 132 4).all rowLinkOK = true := by decide +kernel

theorem rowLink34 : (List.range' 136 4).all rowLinkOK = true := by decide +kernel

theorem rowLink35 : (List.range' 140 4).all rowLinkOK = true := by decide +kernel

theorem rowLink36 : (List.range' 144 4).all rowLinkOK = true := by decide +kernel

theorem rowLink37 : (List.range' 148 4).all rowLinkOK = true := by decide +kernel

theorem rowLink38 : (List.range' 152 4).all rowLinkOK = true := by decide +kernel

theorem rowLink39 : (List.range' 156 4).all rowLinkOK = true := by decide +kernel

theorem rowLink40 : (List.range' 160 4).all rowLinkOK = true := by decide +kernel

theorem rowLink41 : (List.range' 164 4).all rowLinkOK = true := by decide +kernel

theorem rowLink42 : (List.range' 168 4).all rowLinkOK = true := by decide +kernel

theorem rowLink43 : (List.range' 172 4).all rowLinkOK = true := by decide +kernel

theorem rowLink44 : (List.range' 176 4).all rowLinkOK = true := by decide +kernel

theorem rowLink45 : (List.range' 180 4).all rowLinkOK = true := by decide +kernel

theorem rowLink46 : (List.range' 184 4).all rowLinkOK = true := by decide +kernel

theorem rowLink47 : (List.range' 188 4).all rowLinkOK = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
