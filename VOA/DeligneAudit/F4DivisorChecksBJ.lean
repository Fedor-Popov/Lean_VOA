/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 61)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_col_0 : colCheck br colS 52 0 = true := by decide +kernel

theorem f4_col_1 : colCheck br colS 52 1 = true := by decide +kernel

theorem f4_col_2 : colCheck br colS 52 2 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
