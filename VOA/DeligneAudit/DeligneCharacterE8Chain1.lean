/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8Chain0

/-! `E₈`: the pinned intermediate Demazure character `P_1` of `C_1` (one light `decide +kernel`). -/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

set_option maxHeartbeats 4000000 in
/-- `P_1`. -/
def e8P1 : LPolyL :=
  [(([0, 0, 0, 0, 0, 0, 0, 0], 0), 1), (([2, 3, 4, 6, 5, 4, 3, 1], -1), 1), (([2, 3, 4, 6, 5, 4, 3, 2], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e8_sL1 : demazureFinL cartanE8L 7 e8P0 = e8P1 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.E8L
