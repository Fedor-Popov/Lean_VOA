/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 3)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_1350 : nodeChecks 1350 1500 = true := by decide +kernel

theorem f4_nodes_1500 : nodeChecks 1500 1650 = true := by decide +kernel

theorem f4_nodes_1650 : nodeChecks 1650 1800 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
