/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 63)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_col_6 : colCheck br colS 52 6 = true := by decide +kernel

theorem f4_col_7 : colCheck br colS 52 7 = true := by decide +kernel

theorem f4_col_8 : colCheck br colS 52 8 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
