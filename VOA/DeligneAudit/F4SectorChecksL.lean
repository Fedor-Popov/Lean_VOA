/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU333
import VOA.DeligneAudit.F4SectorChecksU334
import VOA.DeligneAudit.F4SectorChecksU335

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b33 : (List.range' 33 1).all u3OK = true := by
  exact f4_u3_row_33

theorem u3_b34 : (List.range' 34 1).all u3OK = true := by
  exact f4_u3_row_34

theorem u3_b35 : (List.range' 35 1).all u3OK = true := by
  exact f4_u3_row_35


end VOA.DeligneAudit.DeligneSector.F4
