/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 5)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_2250 : nodeChecks 2250 2400 = true := by decide +kernel

theorem f4_nodes_2400 : nodeChecks 2400 2550 = true := by decide +kernel

theorem f4_nodes_2550 : nodeChecks 2550 2700 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
