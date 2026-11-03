/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU300
import VOA.DeligneAudit.F4SectorChecksU301
import VOA.DeligneAudit.F4SectorChecksU302

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b0 : (List.range' 0 1).all u3OK = true := by
  exact f4_u3_row_00

theorem u3_b1 : (List.range' 1 1).all u3OK = true := by
  exact f4_u3_row_01

theorem u3_b2 : (List.range' 2 1).all u3OK = true := by
  exact f4_u3_row_02


end VOA.DeligneAudit.DeligneSector.F4
