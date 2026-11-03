/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8Chain57

/-! `E₈`: invariance check `memθ` on the pinned `C_1` (light). -/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

set_option maxHeartbeats 4000000 in
theorem e8_memθL : memCheckL (reflZeroL cartanE8L thetaE8L) e8P57 = true := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.E8L
