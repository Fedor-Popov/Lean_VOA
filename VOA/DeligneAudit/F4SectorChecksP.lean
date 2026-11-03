/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU345
import VOA.DeligneAudit.F4SectorChecksU346
import VOA.DeligneAudit.F4SectorChecksU347

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b45 : (List.range' 45 1).all u3OK = true := by
  exact f4_u3_row_45

theorem u3_b46 : (List.range' 46 1).all u3OK = true := by
  exact f4_u3_row_46

theorem u3_b47 : (List.range' 47 1).all u3OK = true := by
  exact f4_u3_row_47


end VOA.DeligneAudit.DeligneSector.F4
