/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU306
import VOA.DeligneAudit.F4SectorChecksU307
import VOA.DeligneAudit.F4SectorChecksU308

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b6 : (List.range' 6 1).all u3OK = true := by
  exact f4_u3_row_06

theorem u3_b7 : (List.range' 7 1).all u3OK = true := by
  exact f4_u3_row_07

theorem u3_b8 : (List.range' 8 1).all u3OK = true := by
  exact f4_u3_row_08


end VOA.DeligneAudit.DeligneSector.F4
