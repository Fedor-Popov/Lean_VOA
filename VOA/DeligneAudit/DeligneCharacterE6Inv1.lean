/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE6Inv0

/-! `E₆`: invariance checks on the pinned `C_1` (part 1). -/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

set_option maxHeartbeats 4000000 in
theorem e6_mem2 : memCheck (reflFin cartanE6 2) e6P21 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_mem3 : memCheck (reflFin cartanE6 3) e6P21 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_mem4 : memCheck (reflFin cartanE6 4) e6P21 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_mem5 : memCheck (reflFin cartanE6 5) e6P21 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount
