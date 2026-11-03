/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterE8Light

/-! `E₈`: the pinned intermediate Demazure character `P_0` of `C_1` (one light `decide +kernel`). -/

namespace VOA.DeligneAudit.DeligneCharacter.E8L

set_option maxHeartbeats 4000000 in
/-- `P_0`. -/
def e8P0 : LPolyL :=
  [(([2, 3, 4, 6, 5, 4, 3, 2], -1), 1), (([0, 0, 0, 0, 0, 0, 0, 0], 0), 1)]

set_option maxHeartbeats 4000000 in
theorem e8_sL0 : demazureZeroL cartanE8L thetaE8L [((List.replicate thetaE8L.length 0, 0), 1)] = e8P0 := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.E8L
