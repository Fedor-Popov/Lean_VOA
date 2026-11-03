/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksStabG09R164N16
import VOA.DeligneAudit.F4SectorChecksStabG09R180N16
import VOA.DeligneAudit.F4SectorChecksStabG09R196N16
import VOA.DeligneAudit.F4SectorChecksStabG09R212N16
import VOA.DeligneAudit.F4SectorChecksStabG09R228N16
import VOA.DeligneAudit.F4SectorChecksStabG09R244N02
import VOA.DeligneAudit.F4SectorChecksStabG09R246N16
import VOA.DeligneAudit.F4SectorChecksStabG09R262N16
import VOA.DeligneAudit.F4SectorChecksStabG09R278N16
import VOA.DeligneAudit.F4SectorChecksStabG09R294N16
import VOA.DeligneAudit.F4SectorChecksStabG09R310N15
import VOA.DeligneAudit.F4SectorChecksStabG10R000N16
import VOA.DeligneAudit.F4SectorChecksStabG10R016N16
import VOA.DeligneAudit.F4SectorChecksStabG10R032N16
import VOA.DeligneAudit.F4SectorChecksStabG10R048N16
import VOA.DeligneAudit.F4SectorChecksStabG10R064N16
import VOA.DeligneAudit.F4SectorChecksStabG10R080N02

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem stab_b9_164 : (List.range' 164 82).all (stabCheck 9) = true := by
  exact (f4_range_join 164 48 212 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 164 16 180 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r164_n16
    (f4_range_join 180 16 196 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r180_n16
    f4_stab_g09_r196_n16))
    (f4_range_join 212 16 228 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r212_n16
    (f4_range_join 228 16 244 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r228_n16
    f4_stab_g09_r244_n02)))

theorem stab_b9_246 : (List.range' 246 79).all (stabCheck 9) = true := by
  exact (f4_range_join 246 32 278 47 79 (by decide +kernel) (by decide +kernel)
    (f4_range_join 246 16 262 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r246_n16
    f4_stab_g09_r262_n16)
    (f4_range_join 278 16 294 31 47 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r278_n16
    (f4_range_join 294 16 310 15 31 (by decide +kernel) (by decide +kernel)
    f4_stab_g09_r294_n16
    f4_stab_g09_r310_n15)))

theorem stab_b10_0 : (List.range' 0 82).all (stabCheck 10) = true := by
  exact (f4_range_join 0 48 48 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g10_r000_n16
    (f4_range_join 16 16 32 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g10_r016_n16
    f4_stab_g10_r032_n16))
    (f4_range_join 48 16 64 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g10_r048_n16
    (f4_range_join 64 16 80 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g10_r064_n16
    f4_stab_g10_r080_n02)))


end VOA.DeligneAudit.DeligneSector.F4
