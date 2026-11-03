/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8Chain6

/-! `E₈`: the pinned intermediate Demazure character `P_7` of `C_1` (one light `decide +kernel`). -/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

set_option maxHeartbeats 4000000 in
/-- `P_7`. -/
def e8P7 : LPolyL :=
  [(([0, 0, 0, 0, 0, 0, 0, 0], 0), 1), (([2, 3, 4, 6, 5, 4, 3, 1], -1), 1), (([2, 3, 4, 6, 5, 3, 2, 1], -1), 1), (([2, 3, 3, 5, 4, 3, 2, 1], -1), 1), (([2, 3, 4, 5, 4, 3, 2, 1], -1), 1), (([2, 2, 3, 5, 4, 3, 2, 1], -1), 1), (([2, 2, 4, 5, 4, 3, 2, 1], -1), 1), (([2, 3, 4, 6, 4, 3, 2, 1], -1), 1), (([2, 3, 4, 6, 5, 4, 2, 1], -1), 1), (([2, 3, 4, 6, 5, 4, 3, 2], -1), 1)]

set_option maxHeartbeats 4000000 in
theorem e8_sL7 : demazureFinL cartanE8L 2 e8P6 = e8P7 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.E8L
