/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE7Inv3

/-! `E₇`: invariance checks on the pinned `C_1` (part 4). -/

namespace VOA.DeligneAudit.DeligneCharacter.DemCount

open VOA.DeligneAudit.DeligneCharacter

set_option maxHeartbeats 4000000 in
theorem e7_mem6 : memCheck (reflFin cartanE7 6) e7P33 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount
