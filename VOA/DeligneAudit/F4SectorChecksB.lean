/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU303
import VOA.DeligneAudit.F4SectorChecksU304
import VOA.DeligneAudit.F4SectorChecksU305

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b3 : (List.range' 3 1).all u3OK = true := by
  exact f4_u3_row_03

theorem u3_b4 : (List.range' 4 1).all u3OK = true := by
  exact f4_u3_row_04

theorem u3_b5 : (List.range' 5 1).all u3OK = true := by
  exact f4_u3_row_05


end VOA.DeligneAudit.DeligneSector.F4
