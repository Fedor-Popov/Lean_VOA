/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8Chain2

/-! `E₈`: the pinned intermediate Demazure character `P_3` of `C_1` (one light `decide +kernel`). -/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

set_option maxHeartbeats 4000000 in
/-- `P_3`. -/
def e8P3 : LPolyL :=
  [(([0, 0, 0, 0, 0, 0, 0, 0], 0), 1), (([2, 3, 4, 6, 5, 4, 3, 1], -1), 1), (([2, 3, 4, 6, 5, 3, 2, 1], -1), 1), (([2, 3, 4, 6, 5, 4, 2, 1], -1), 1), (([2, 3, 4, 6, 5, 4, 3, 2], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e8_sL3 : demazureFinL cartanE8L 5 e8P2 = e8P3 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.E8L
