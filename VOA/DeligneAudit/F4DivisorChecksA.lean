/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 0)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_1 : nodeChecks 1 150 = true := by decide +kernel

theorem f4_nodes_150 : nodeChecks 150 300 = true := by decide +kernel

theorem f4_nodes_300 : nodeChecks 300 450 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
