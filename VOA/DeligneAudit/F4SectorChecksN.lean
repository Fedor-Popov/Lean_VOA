/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU339
import VOA.DeligneAudit.F4SectorChecksU340
import VOA.DeligneAudit.F4SectorChecksU341

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b39 : (List.range' 39 1).all u3OK = true := by
  exact f4_u3_row_39

theorem u3_b40 : (List.range' 40 1).all u3OK = true := by
  exact f4_u3_row_40

theorem u3_b41 : (List.range' 41 1).all u3OK = true := by
  exact f4_u3_row_41


end VOA.DeligneAudit.DeligneSector.F4
