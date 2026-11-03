/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2DivisorData

/-!
# G2 pair-comparison certificates: kernel checks (blocks 6)
-/

namespace VOA.DeligneAudit.DeligneDivisor.G2

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.G2 (br relZ)

theorem g2_col_10 : colCheck br colS 14 10 = true := by decide +kernel

theorem g2_col_11 : colCheck br colS 14 11 = true := by decide +kernel

theorem g2_col_12 : colCheck br colS 14 12 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.G2
