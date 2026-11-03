/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksU351
import VOA.DeligneAudit.F4SectorChecksStabG00R000N16
import VOA.DeligneAudit.F4SectorChecksStabG00R016N16
import VOA.DeligneAudit.F4SectorChecksStabG00R032N16
import VOA.DeligneAudit.F4SectorChecksStabG00R048N16
import VOA.DeligneAudit.F4SectorChecksStabG00R064N16
import VOA.DeligneAudit.F4SectorChecksStabG00R080N02
import VOA.DeligneAudit.F4SectorChecksStabG00R082N16
import VOA.DeligneAudit.F4SectorChecksStabG00R098N16
import VOA.DeligneAudit.F4SectorChecksStabG00R114N16
import VOA.DeligneAudit.F4SectorChecksStabG00R130N16
import VOA.DeligneAudit.F4SectorChecksStabG00R146N16
import VOA.DeligneAudit.F4SectorChecksStabG00R162N02

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b51 : (List.range' 51 1).all u3OK = true := by
  exact f4_u3_row_51

theorem stab_b0_0 : (List.range' 0 82).all (stabCheck 0) = true := by
  exact (f4_range_join 0 48 48 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r000_n16
    (f4_range_join 16 16 32 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r016_n16
    f4_stab_g00_r032_n16))
    (f4_range_join 48 16 64 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r048_n16
    (f4_range_join 64 16 80 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r064_n16
    f4_stab_g00_r080_n02)))

theorem stab_b0_82 : (List.range' 82 82).all (stabCheck 0) = true := by
  exact (f4_range_join 82 48 130 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 82 16 98 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r082_n16
    (f4_range_join 98 16 114 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r098_n16
    f4_stab_g00_r114_n16))
    (f4_range_join 130 16 146 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r130_n16
    (f4_range_join 146 16 162 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g00_r146_n16
    f4_stab_g00_r162_n02)))


end VOA.DeligneAudit.DeligneSector.F4
