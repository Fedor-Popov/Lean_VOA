/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksStabG07R082N16
import VOA.DeligneAudit.F4SectorChecksStabG07R098N16
import VOA.DeligneAudit.F4SectorChecksStabG07R114N16
import VOA.DeligneAudit.F4SectorChecksStabG07R130N16
import VOA.DeligneAudit.F4SectorChecksStabG07R146N16
import VOA.DeligneAudit.F4SectorChecksStabG07R162N02
import VOA.DeligneAudit.F4SectorChecksStabG07R164N16
import VOA.DeligneAudit.F4SectorChecksStabG07R180N16
import VOA.DeligneAudit.F4SectorChecksStabG07R196N16
import VOA.DeligneAudit.F4SectorChecksStabG07R212N16
import VOA.DeligneAudit.F4SectorChecksStabG07R228N16
import VOA.DeligneAudit.F4SectorChecksStabG07R244N02
import VOA.DeligneAudit.F4SectorChecksStabG07R246N16
import VOA.DeligneAudit.F4SectorChecksStabG07R262N16
import VOA.DeligneAudit.F4SectorChecksStabG07R278N16
import VOA.DeligneAudit.F4SectorChecksStabG07R294N16
import VOA.DeligneAudit.F4SectorChecksStabG07R310N15

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem stab_b7_82 : (List.range' 82 82).all (stabCheck 7) = true := by
  exact (f4_range_join 82 48 130 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 82 16 98 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r082_n16
    (f4_range_join 98 16 114 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r098_n16
    f4_stab_g07_r114_n16))
    (f4_range_join 130 16 146 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r130_n16
    (f4_range_join 146 16 162 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r146_n16
    f4_stab_g07_r162_n02)))

theorem stab_b7_164 : (List.range' 164 82).all (stabCheck 7) = true := by
  exact (f4_range_join 164 48 212 34 82 (by decide +kernel) (by decide +kernel)
    (f4_range_join 164 16 180 32 48 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r164_n16
    (f4_range_join 180 16 196 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r180_n16
    f4_stab_g07_r196_n16))
    (f4_range_join 212 16 228 18 34 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r212_n16
    (f4_range_join 228 16 244 2 18 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r228_n16
    f4_stab_g07_r244_n02)))

theorem stab_b7_246 : (List.range' 246 79).all (stabCheck 7) = true := by
  exact (f4_range_join 246 32 278 47 79 (by decide +kernel) (by decide +kernel)
    (f4_range_join 246 16 262 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r246_n16
    f4_stab_g07_r262_n16)
    (f4_range_join 278 16 294 31 47 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r278_n16
    (f4_range_join 294 16 310 15 31 (by decide +kernel) (by decide +kernel)
    f4_stab_g07_r294_n16
    f4_stab_g07_r310_n15)))


end VOA.DeligneAudit.DeligneSector.F4
