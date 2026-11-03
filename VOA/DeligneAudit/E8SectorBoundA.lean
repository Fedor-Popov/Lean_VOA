/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` sector: index bounds of the table (chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.AffineGeneral.SCLie

theorem e8_bound0 : boundChunk e8T 248 0 4 = true := by decide +kernel
theorem e8_bound1 : boundChunk e8T 248 4 8 = true := by decide +kernel
theorem e8_bound2 : boundChunk e8T 248 8 12 = true := by decide +kernel
theorem e8_bound3 : boundChunk e8T 248 12 16 = true := by decide +kernel
theorem e8_bound4 : boundChunk e8T 248 16 20 = true := by decide +kernel
theorem e8_bound5 : boundChunk e8T 248 20 24 = true := by decide +kernel
theorem e8_bound6 : boundChunk e8T 248 24 28 = true := by decide +kernel
theorem e8_bound7 : boundChunk e8T 248 28 32 = true := by decide +kernel
theorem e8_bound8 : boundChunk e8T 248 32 36 = true := by decide +kernel
theorem e8_bound9 : boundChunk e8T 248 36 40 = true := by decide +kernel
theorem e8_bound10 : boundChunk e8T 248 40 44 = true := by decide +kernel
theorem e8_bound11 : boundChunk e8T 248 44 48 = true := by decide +kernel
theorem e8_bound12 : boundChunk e8T 248 48 52 = true := by decide +kernel
theorem e8_bound13 : boundChunk e8T 248 52 56 = true := by decide +kernel
theorem e8_bound14 : boundChunk e8T 248 56 60 = true := by decide +kernel
theorem e8_bound15 : boundChunk e8T 248 60 64 = true := by decide +kernel
theorem e8_bound16 : boundChunk e8T 248 64 68 = true := by decide +kernel
theorem e8_bound17 : boundChunk e8T 248 68 72 = true := by decide +kernel
theorem e8_bound18 : boundChunk e8T 248 72 76 = true := by decide +kernel
theorem e8_bound19 : boundChunk e8T 248 76 80 = true := by decide +kernel
theorem e8_bound20 : boundChunk e8T 248 80 84 = true := by decide +kernel
theorem e8_bound21 : boundChunk e8T 248 84 88 = true := by decide +kernel
theorem e8_bound22 : boundChunk e8T 248 88 92 = true := by decide +kernel
theorem e8_bound23 : boundChunk e8T 248 92 96 = true := by decide +kernel
theorem e8_bound24 : boundChunk e8T 248 96 100 = true := by decide +kernel
theorem e8_bound25 : boundChunk e8T 248 100 104 = true := by decide +kernel
theorem e8_bound26 : boundChunk e8T 248 104 108 = true := by decide +kernel
theorem e8_bound27 : boundChunk e8T 248 108 112 = true := by decide +kernel
theorem e8_bound28 : boundChunk e8T 248 112 116 = true := by decide +kernel
theorem e8_bound29 : boundChunk e8T 248 116 120 = true := by decide +kernel
theorem e8_bound30 : boundChunk e8T 248 120 124 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
