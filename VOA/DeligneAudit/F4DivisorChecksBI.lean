/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 60)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_depth : depthCheck = true := by decide +kernel

theorem f4_root : tab 0 = [(45, 45, 1)] ∧ par 0 = (0, false, 0, 0, 0) := by decide +kernel

theorem f4_psiComplete : psiComplete = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
