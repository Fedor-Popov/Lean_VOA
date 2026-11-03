/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2DivisorData

/-!
# G2 pair-comparison certificates: kernel checks (blocks 3)
-/

namespace VOA.DeligneAudit.DeligneDivisor.G2

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.G2 (br relZ)

theorem g2_col_1 : colCheck br colS 14 1 = true := by decide +kernel

theorem g2_col_2 : colCheck br colS 14 2 = true := by decide +kernel

theorem g2_col_3 : colCheck br colS 14 3 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.G2
