/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU321
import VOA.DeligneAudit.F4SectorChecksU322
import VOA.DeligneAudit.F4SectorChecksU323

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b21 : (List.range' 21 1).all u3OK = true := by
  exact f4_u3_row_21

theorem u3_b22 : (List.range' 22 1).all u3OK = true := by
  exact f4_u3_row_22

theorem u3_b23 : (List.range' 23 1).all u3OK = true := by
  exact f4_u3_row_23


end VOA.DeligneAudit.DeligneSector.F4
