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

theorem wtChunk_31 : wtChunk 124 128 = true := by decide +kernel
theorem wtChunk_32 : wtChunk 128 132 = true := by decide +kernel
theorem wtChunk_33 : wtChunk 132 136 = true := by decide +kernel
theorem wtChunk_34 : wtChunk 136 140 = true := by decide +kernel
theorem wtChunk_35 : wtChunk 140 144 = true := by decide +kernel
theorem wtChunk_36 : wtChunk 144 148 = true := by decide +kernel
theorem wtChunk_37 : wtChunk 148 152 = true := by decide +kernel
theorem wtChunk_38 : wtChunk 152 156 = true := by decide +kernel
theorem wtChunk_39 : wtChunk 156 160 = true := by decide +kernel
theorem wtChunk_40 : wtChunk 160 164 = true := by decide +kernel
theorem wtChunk_41 : wtChunk 164 168 = true := by decide +kernel
theorem wtChunk_42 : wtChunk 168 172 = true := by decide +kernel
theorem wtChunk_43 : wtChunk 172 176 = true := by decide +kernel
theorem wtChunk_44 : wtChunk 176 180 = true := by decide +kernel
theorem wtChunk_45 : wtChunk 180 184 = true := by decide +kernel
theorem wtChunk_46 : wtChunk 184 188 = true := by decide +kernel
theorem wtChunk_47 : wtChunk 188 192 = true := by decide +kernel
theorem wtChunk_48 : wtChunk 192 196 = true := by decide +kernel
theorem wtChunk_49 : wtChunk 196 200 = true := by decide +kernel
theorem wtChunk_50 : wtChunk 200 204 = true := by decide +kernel
theorem wtChunk_51 : wtChunk 204 208 = true := by decide +kernel
theorem wtChunk_52 : wtChunk 208 212 = true := by decide +kernel
theorem wtChunk_53 : wtChunk 212 216 = true := by decide +kernel
theorem wtChunk_54 : wtChunk 216 220 = true := by decide +kernel
theorem wtChunk_55 : wtChunk 220 224 = true := by decide +kernel
theorem wtChunk_56 : wtChunk 224 228 = true := by decide +kernel
theorem wtChunk_57 : wtChunk 228 232 = true := by decide +kernel
theorem wtChunk_58 : wtChunk 232 236 = true := by decide +kernel
theorem wtChunk_59 : wtChunk 236 240 = true := by decide +kernel
theorem wtChunk_60 : wtChunk 240 244 = true := by decide +kernel
theorem wtChunk_61 : wtChunk 244 248 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
