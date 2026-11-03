/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecks

/-!
# `E₇` sector: weight additivity of the table (chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem wtChunk_0 : wtChunk 0 19 = true := by decide +kernel
theorem wtChunk_1 : wtChunk 19 38 = true := by decide +kernel
theorem wtChunk_2 : wtChunk 38 57 = true := by decide +kernel
theorem wtChunk_3 : wtChunk 57 76 = true := by decide +kernel
theorem wtChunk_4 : wtChunk 76 95 = true := by decide +kernel
theorem wtChunk_5 : wtChunk 95 114 = true := by decide +kernel
theorem wtChunk_6 : wtChunk 114 133 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E7
