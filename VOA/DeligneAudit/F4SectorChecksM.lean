/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU336
import VOA.DeligneAudit.F4SectorChecksU337
import VOA.DeligneAudit.F4SectorChecksU338

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b36 : (List.range' 36 1).all u3OK = true := by
  exact f4_u3_row_36

theorem u3_b37 : (List.range' 37 1).all u3OK = true := by
  exact f4_u3_row_37

theorem u3_b38 : (List.range' 38 1).all u3OK = true := by
  exact f4_u3_row_38


end VOA.DeligneAudit.DeligneSector.F4
