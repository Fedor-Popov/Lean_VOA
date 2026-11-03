/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU309
import VOA.DeligneAudit.F4SectorChecksU310
import VOA.DeligneAudit.F4SectorChecksU311

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b9 : (List.range' 9 1).all u3OK = true := by
  exact f4_u3_row_09

theorem u3_b10 : (List.range' 10 1).all u3OK = true := by
  exact f4_u3_row_10

theorem u3_b11 : (List.range' 11 1).all u3OK = true := by
  exact f4_u3_row_11


end VOA.DeligneAudit.DeligneSector.F4
