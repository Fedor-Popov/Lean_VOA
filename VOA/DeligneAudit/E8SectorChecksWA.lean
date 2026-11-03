/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorChecks

/-!
# `E₈` sector: weight additivity of the table (chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral.SCLie

theorem wtChunk_0 : wtChunk 0 4 = true := by decide +kernel
theorem wtChunk_1 : wtChunk 4 8 = true := by decide +kernel
theorem wtChunk_2 : wtChunk 8 12 = true := by decide +kernel
theorem wtChunk_3 : wtChunk 12 16 = true := by decide +kernel
theorem wtChunk_4 : wtChunk 16 20 = true := by decide +kernel
theorem wtChunk_5 : wtChunk 20 24 = true := by decide +kernel
theorem wtChunk_6 : wtChunk 24 28 = true := by decide +kernel
theorem wtChunk_7 : wtChunk 28 32 = true := by decide +kernel
theorem wtChunk_8 : wtChunk 32 36 = true := by decide +kernel
theorem wtChunk_9 : wtChunk 36 40 = true := by decide +kernel
theorem wtChunk_10 : wtChunk 40 44 = true := by decide +kernel
theorem wtChunk_11 : wtChunk 44 48 = true := by decide +kernel
theorem wtChunk_12 : wtChunk 48 52 = true := by decide +kernel
theorem wtChunk_13 : wtChunk 52 56 = true := by decide +kernel
theorem wtChunk_14 : wtChunk 56 60 = true := by decide +kernel
theorem wtChunk_15 : wtChunk 60 64 = true := by decide +kernel
theorem wtChunk_16 : wtChunk 64 68 = true := by decide +kernel
theorem wtChunk_17 : wtChunk 68 72 = true := by decide +kernel
theorem wtChunk_18 : wtChunk 72 76 = true := by decide +kernel
theorem wtChunk_19 : wtChunk 76 80 = true := by decide +kernel
theorem wtChunk_20 : wtChunk 80 84 = true := by decide +kernel
theorem wtChunk_21 : wtChunk 84 88 = true := by decide +kernel
theorem wtChunk_22 : wtChunk 88 92 = true := by decide +kernel
theorem wtChunk_23 : wtChunk 92 96 = true := by decide +kernel
theorem wtChunk_24 : wtChunk 96 100 = true := by decide +kernel
theorem wtChunk_25 : wtChunk 100 104 = true := by decide +kernel
theorem wtChunk_26 : wtChunk 104 108 = true := by decide +kernel
theorem wtChunk_27 : wtChunk 108 112 = true := by decide +kernel
theorem wtChunk_28 : wtChunk 112 116 = true := by decide +kernel
theorem wtChunk_29 : wtChunk 116 120 = true := by decide +kernel
theorem wtChunk_30 : wtChunk 120 124 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
