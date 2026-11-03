/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU348
import VOA.DeligneAudit.F4SectorChecksU349
import VOA.DeligneAudit.F4SectorChecksU350

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b48 : (List.range' 48 1).all u3OK = true := by
  exact f4_u3_row_48

theorem u3_b49 : (List.range' 49 1).all u3OK = true := by
  exact f4_u3_row_49

theorem u3_b50 : (List.range' 50 1).all u3OK = true := by
  exact f4_u3_row_50


end VOA.DeligneAudit.DeligneSector.F4
