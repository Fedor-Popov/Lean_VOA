/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorU3Data

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

theorem f4_u3_row_42 : (List.range' 42 1).all u3OK = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneSector.F4
