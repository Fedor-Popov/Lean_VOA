/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU315
import VOA.DeligneAudit.F4SectorChecksU316
import VOA.DeligneAudit.F4SectorChecksU317

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b15 : (List.range' 15 1).all u3OK = true := by
  exact f4_u3_row_15

theorem u3_b16 : (List.range' 16 1).all u3OK = true := by
  exact f4_u3_row_16

theorem u3_b17 : (List.range' 17 1).all u3OK = true := by
  exact f4_u3_row_17


end VOA.DeligneAudit.DeligneSector.F4
