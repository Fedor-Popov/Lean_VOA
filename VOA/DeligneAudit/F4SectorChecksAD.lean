/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksStabG08R246N16
import VOA.DeligneAudit.F4SectorChecksStabG08R262N16
import VOA.DeligneAudit.F4SectorChecksStabG08R278N16
import VOA.DeligneAudit.F4SectorChecksStabG08R294N16
import VOA.DeligneAudit.F4SectorChecksStabG08R310N15
import VOA.DeligneAudit.F4SectorChecksStabG09R000N16
import VOA.DeligneAudit.F4SectorChecksStabG09R016N16
import VOA.DeligneAudit.F4SectorChecksStabG09R032N16
import VOA.DeligneAudit.F4SectorChecksStabG09R048N16
import VOA.DeligneAudit.F4SectorChecksStabG09R064N16
import VOA.DeligneAudit.F4SectorChecksStabG09R080N02
import VOA.DeligneAudit.F4SectorChecksStabG09R082N16
import VOA.DeligneAudit.F4SectorChecksStabG09R098N16
import VOA.DeligneAudit.F4SectorChecksStabG09R114N16
import VOA.DeligneAudit.F4SectorChecksStabG09R130N16
import VOA.DeligneAudit.F4SectorChecksStabG09R146N16
import VOA.DeligneAudit.F4SectorChecksStabG09R162N02

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem stab_b8_246 : (List.range' 246 79).all (stabCheck 8) = true := by
  exact (f4_range_join 246 32 278 47 79 (by decide +kernel) (by decide +kernel)
    (f4_range_join 246 16 262 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g08_r246_n16
    f4_stab_g08_r262_n16)
    (f4_range_join 278 16 294 31 47 (by decide +kernel) (by decide +kernel)
    f4_stab_g08_r278_n16
    (f4_range_join 294 16 310 15 31 (by decide +kernel) (by decide +kernel)
    f4_stab_g08_r294_n16
    f4_stab_g08_r310_n15)))

theorem stab_b9_0 : (List.range' 0 82).all (stabCheck 9) = true := by
  exact (f4_range_join 0 48 48 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r000_n16
    (f4_range_join 16 16 32 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r016_n16
    f4_stab_g09_r032_n16))
    (f4_range_join 48 16 64 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r048_n16
    (f4_range_join 64 16 80 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r064_n16
    f4_stab_g09_r080_n02)))

theorem stab_b9_82 : (List.range' 82 82).all (stabCheck 9) = true := by
  exact (f4_range_join 82 48 130 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 82 16 98 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r082_n16
    (f4_range_join 98 16 114 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r098_n16
    f4_stab_g09_r114_n16))
    (f4_range_join 130 16 146 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r130_n16
    (f4_range_join 146 16 162 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r146_n16
    f4_stab_g09_r162_n02)))


end VOA.DeligneAudit.DeligneSector.F4
