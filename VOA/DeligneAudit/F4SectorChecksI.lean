/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU324
import VOA.DeligneAudit.F4SectorChecksU325
import VOA.DeligneAudit.F4SectorChecksU326

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b24 : (List.range' 24 1).all u3OK = true := by
  exact f4_u3_row_24

theorem u3_b25 : (List.range' 25 1).all u3OK = true := by
  exact f4_u3_row_25

theorem u3_b26 : (List.range' 26 1).all u3OK = true := by
  exact f4_u3_row_26


end VOA.DeligneAudit.DeligneSector.F4
