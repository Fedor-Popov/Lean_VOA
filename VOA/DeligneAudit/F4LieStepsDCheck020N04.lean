/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSteps

/-! Four fixed-index F4 propagation checks, block D. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

theorem f4_step_d_r020_n04 :
    (List.range' 20 4).all (fun i => stepOK (f4StepsD.getD i (0, 0, 0))) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneSector.F4
