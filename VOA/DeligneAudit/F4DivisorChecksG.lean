/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 6)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_nodes_2700 : nodeChecks 2700 2704 = true := by decide +kernel

theorem f4_U_0 : (List.range' 0 52).all UCheck = true := by decide +kernel

theorem f4_U_52 : (List.range' 52 52).all UCheck = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
