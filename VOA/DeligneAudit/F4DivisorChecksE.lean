/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 4)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_1800 : nodeChecks 1800 1950 = true := by decide +kernel

theorem f4_nodes_1950 : nodeChecks 1950 2100 = true := by decide +kernel

theorem f4_nodes_2100 : nodeChecks 2100 2250 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
