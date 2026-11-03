/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksStabG05R000N16
import VOA.DeligneAudit.F4SectorChecksStabG05R016N16
import VOA.DeligneAudit.F4SectorChecksStabG05R032N16
import VOA.DeligneAudit.F4SectorChecksStabG05R048N16
import VOA.DeligneAudit.F4SectorChecksStabG05R064N16
import VOA.DeligneAudit.F4SectorChecksStabG05R080N02
import VOA.DeligneAudit.F4SectorChecksStabG05R082N16
import VOA.DeligneAudit.F4SectorChecksStabG05R098N16
import VOA.DeligneAudit.F4SectorChecksStabG05R114N16
import VOA.DeligneAudit.F4SectorChecksStabG05R130N16
import VOA.DeligneAudit.F4SectorChecksStabG05R146N16
import VOA.DeligneAudit.F4SectorChecksStabG05R162N02
import VOA.DeligneAudit.F4SectorChecksStabG05R164N16
import VOA.DeligneAudit.F4SectorChecksStabG05R180N16
import VOA.DeligneAudit.F4SectorChecksStabG05R196N16
import VOA.DeligneAudit.F4SectorChecksStabG05R212N16
import VOA.DeligneAudit.F4SectorChecksStabG05R228N16
import VOA.DeligneAudit.F4SectorChecksStabG05R244N02

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem stab_b5_0 : (List.range' 0 82).all (stabCheck 5) = true := by
  exact (f4_range_join 0 48 48 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r000_n16
    (f4_range_join 16 16 32 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r016_n16
    f4_stab_g05_r032_n16))
    (f4_range_join 48 16 64 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r048_n16
    (f4_range_join 64 16 80 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r064_n16
    f4_stab_g05_r080_n02)))

theorem stab_b5_82 : (List.range' 82 82).all (stabCheck 5) = true := by
  exact (f4_range_join 82 48 130 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 82 16 98 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r082_n16
    (f4_range_join 98 16 114 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r098_n16
    f4_stab_g05_r114_n16))
    (f4_range_join 130 16 146 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r130_n16
    (f4_range_join 146 16 162 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r146_n16
    f4_stab_g05_r162_n02)))

theorem stab_b5_164 : (List.range' 164 82).all (stabCheck 5) = true := by
  exact (f4_range_join 164 48 212 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 164 16 180 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r164_n16
    (f4_range_join 180 16 196 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r180_n16
    f4_stab_g05_r196_n16))
    (f4_range_join 212 16 228 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r212_n16
    (f4_range_join 228 16 244 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g05_r228_n16
    f4_stab_g05_r244_n02)))


end VOA.DeligneAudit.DeligneSector.F4
