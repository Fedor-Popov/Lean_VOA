/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE7Chain2

/-! `E₇`: invariance checks on the pinned `C_1` (part 0). -/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

set_option maxHeartbeats 4000000 in
theorem e7_nodup : e7P33.Nodup := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem e7_memθ : memCheck (reflZero cartanE7 thetaE7) e7P33 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount
