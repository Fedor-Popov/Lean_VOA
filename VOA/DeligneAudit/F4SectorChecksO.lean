/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU342
import VOA.DeligneAudit.F4SectorChecksU343
import VOA.DeligneAudit.F4SectorChecksU344

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b42 : (List.range' 42 1).all u3OK = true := by
  exact f4_u3_row_42

theorem u3_b43 : (List.range' 43 1).all u3OK = true := by
  exact f4_u3_row_43

theorem u3_b44 : (List.range' 44 1).all u3OK = true := by
  exact f4_u3_row_44


end VOA.DeligneAudit.DeligneSector.F4
