/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU318
import VOA.DeligneAudit.F4SectorChecksU319
import VOA.DeligneAudit.F4SectorChecksU320

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b18 : (List.range' 18 1).all u3OK = true := by
  exact f4_u3_row_18

theorem u3_b19 : (List.range' 19 1).all u3OK = true := by
  exact f4_u3_row_19

theorem u3_b20 : (List.range' 20 1).all u3OK = true := by
  exact f4_u3_row_20


end VOA.DeligneAudit.DeligneSector.F4
