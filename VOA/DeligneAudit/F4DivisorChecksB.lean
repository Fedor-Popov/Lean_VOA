/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 1)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_450 : nodeChecks 450 600 = true := by decide +kernel

theorem f4_nodes_600 : nodeChecks 600 750 = true := by decide +kernel

theorem f4_nodes_750 : nodeChecks 750 900 = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
