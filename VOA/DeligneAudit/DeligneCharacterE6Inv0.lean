/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE6Chain0

/-! `E₆`: invariance checks on the pinned `C_1` (part 0). -/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

set_option maxHeartbeats 4000000 in
theorem e6_nodup : e6P21.Nodup := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_memθ : memCheck (reflZero cartanE6 thetaE6) e6P21 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_mem0 : memCheck (reflFin cartanE6 0) e6P21 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e6_mem1 : memCheck (reflFin cartanE6 1) e6P21 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount
