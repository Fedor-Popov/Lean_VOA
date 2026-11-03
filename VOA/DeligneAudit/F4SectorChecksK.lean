/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU330
import VOA.DeligneAudit.F4SectorChecksU331
import VOA.DeligneAudit.F4SectorChecksU332

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b30 : (List.range' 30 1).all u3OK = true := by
  exact f4_u3_row_30

theorem u3_b31 : (List.range' 31 1).all u3OK = true := by
  exact f4_u3_row_31

theorem u3_b32 : (List.range' 32 1).all u3OK = true := by
  exact f4_u3_row_32


end VOA.DeligneAudit.DeligneSector.F4
