/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksGenerationRow00
import VOA.DeligneAudit.F4SectorChecksGenerationRow01
import VOA.DeligneAudit.F4SectorChecksGenerationRow02
import VOA.DeligneAudit.F4SectorChecksGenerationRow03
import VOA.DeligneAudit.F4SectorChecksGenerationRow04
import VOA.DeligneAudit.F4SectorChecksGenerationRow05
import VOA.DeligneAudit.F4SectorChecksGenerationRow06
import VOA.DeligneAudit.F4SectorChecksGenerationRow07
import VOA.DeligneAudit.F4SectorChecksGenerationRow08
import VOA.DeligneAudit.F4SectorChecksGenerationRow09
import VOA.DeligneAudit.F4SectorChecksGenerationRow10
import VOA.DeligneAudit.F4SectorChecksGenerationRow11
import VOA.DeligneAudit.F4SectorChecksGenerationRow12
import VOA.DeligneAudit.F4SectorChecksGenerationRow13
import VOA.DeligneAudit.F4SectorChecksGenerationRow14
import VOA.DeligneAudit.F4SectorChecksGenerationRow15
import VOA.DeligneAudit.F4SectorChecksGenerationRow16
import VOA.DeligneAudit.F4SectorChecksGenerationRow17
import VOA.DeligneAudit.F4SectorChecksGenerationRow18
import VOA.DeligneAudit.F4SectorChecksGenerationRow19
import VOA.DeligneAudit.F4SectorChecksGenerationRow20
import VOA.DeligneAudit.F4SectorChecksGenerationRow21
import VOA.DeligneAudit.F4SectorChecksGenerationRow22
import VOA.DeligneAudit.F4SectorChecksGenerationRow23
import VOA.DeligneAudit.F4SectorChecksGenerationRow24
import VOA.DeligneAudit.F4SectorChecksGenerationRow25
import VOA.DeligneAudit.F4SectorChecksGenerationRow26
import VOA.DeligneAudit.F4SectorChecksGenerationRow27
import VOA.DeligneAudit.F4SectorChecksGenerationRow28
import VOA.DeligneAudit.F4SectorChecksGenerationRow29
import VOA.DeligneAudit.F4SectorChecksGenerationRow30
import VOA.DeligneAudit.F4SectorChecksGenerationRow31
import VOA.DeligneAudit.F4SectorChecksGenerationRow32
import VOA.DeligneAudit.F4SectorChecksGenerationRow33
import VOA.DeligneAudit.F4SectorChecksGenerationRow34
import VOA.DeligneAudit.F4SectorChecksGenerationRow35
import VOA.DeligneAudit.F4SectorChecksGenerationRow36
import VOA.DeligneAudit.F4SectorChecksGenerationRow37
import VOA.DeligneAudit.F4SectorChecksGenerationRow38
import VOA.DeligneAudit.F4SectorChecksGenerationRow39
import VOA.DeligneAudit.F4SectorChecksCover
import VOA.DeligneAudit.F4SectorChecksDiagR000N16
import VOA.DeligneAudit.F4SectorChecksDiagR016N16
import VOA.DeligneAudit.F4SectorChecksDiagR032N16
import VOA.DeligneAudit.F4SectorChecksDiagR048N16
import VOA.DeligneAudit.F4SectorChecksDiagR064N16
import VOA.DeligneAudit.F4SectorChecksDiagR080N16
import VOA.DeligneAudit.F4SectorChecksDiagR096N16
import VOA.DeligneAudit.F4SectorChecksDiagR112N16
import VOA.DeligneAudit.F4SectorChecksDiagR128N16
import VOA.DeligneAudit.F4SectorChecksDiagR144N16
import VOA.DeligneAudit.F4SectorChecksDiagR160N16
import VOA.DeligneAudit.F4SectorChecksDiagR176N16
import VOA.DeligneAudit.F4SectorChecksDiagR192N16
import VOA.DeligneAudit.F4SectorChecksDiagR208N16
import VOA.DeligneAudit.F4SectorChecksDiagR224N16
import VOA.DeligneAudit.F4SectorChecksDiagR240N16
import VOA.DeligneAudit.F4SectorChecksDiagR256N16
import VOA.DeligneAudit.F4SectorChecksDiagR272N16
import VOA.DeligneAudit.F4SectorChecksDiagR288N16
import VOA.DeligneAudit.F4SectorChecksDiagR304N16
import VOA.DeligneAudit.F4SectorChecksDiagR320N05

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem gen_ok : genCheck 52 br genT gensL = true := by
    apply f4_genCheck_of_rows
    intro i hi
    have hlen : genT.length = 40 := by decide +kernel
    rw [hlen] at hi
    interval_cases i
    · exact f4_generation_row_00
    · exact f4_generation_row_01
    · exact f4_generation_row_02
    · exact f4_generation_row_03
    · exact f4_generation_row_04
    · exact f4_generation_row_05
    · exact f4_generation_row_06
    · exact f4_generation_row_07
    · exact f4_generation_row_08
    · exact f4_generation_row_09
    · exact f4_generation_row_10
    · exact f4_generation_row_11
    · exact f4_generation_row_12
    · exact f4_generation_row_13
    · exact f4_generation_row_14
    · exact f4_generation_row_15
    · exact f4_generation_row_16
    · exact f4_generation_row_17
    · exact f4_generation_row_18
    · exact f4_generation_row_19
    · exact f4_generation_row_20
    · exact f4_generation_row_21
    · exact f4_generation_row_22
    · exact f4_generation_row_23
    · exact f4_generation_row_24
    · exact f4_generation_row_25
    · exact f4_generation_row_26
    · exact f4_generation_row_27
    · exact f4_generation_row_28
    · exact f4_generation_row_29
    · exact f4_generation_row_30
    · exact f4_generation_row_31
    · exact f4_generation_row_32
    · exact f4_generation_row_33
    · exact f4_generation_row_34
    · exact f4_generation_row_35
    · exact f4_generation_row_36
    · exact f4_generation_row_37
    · exact f4_generation_row_38
    · exact f4_generation_row_39

theorem cover_ok :
    ((List.range 52).all fun c => decide (c ∈ gensL ++ genT.map (·.1))) = true := by
  exact f4_cover_rows

theorem diag_ok :
    ((List.range 325).all fun k => (relZ k).all fun t => !(t.1 = 45 ∧ t.2.1 = 45)) = true := by
    rw [List.range_eq_range']
    exact (f4_range_join 0 160 160 165 325 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 80 80 80 160 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 32 32 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r000_n16
    f4_diag_r016_n16)
    (f4_range_join 32 16 48 32 48 (by decide +kernel) (by decide +kernel)
    f4_diag_r032_n16
    (f4_range_join 48 16 64 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r048_n16
    f4_diag_r064_n16)))
    (f4_range_join 80 32 112 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 80 16 96 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r080_n16
    f4_diag_r096_n16)
    (f4_range_join 112 16 128 32 48 (by decide +kernel) (by decide +kernel)
    f4_diag_r112_n16
    (f4_range_join 128 16 144 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r128_n16
    f4_diag_r144_n16))))
    (f4_range_join 160 80 240 85 165 (by decide +kernel) (by decide +kernel)
    (f4_range_join 160 32 192 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 160 16 176 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r160_n16
    f4_diag_r176_n16)
    (f4_range_join 192 16 208 32 48 (by decide +kernel) (by decide +kernel)
    f4_diag_r192_n16
    (f4_range_join 208 16 224 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r208_n16
    f4_diag_r224_n16)))
    (f4_range_join 240 48 288 37 85 (by decide +kernel) (by decide +kernel)
    (f4_range_join 240 16 256 32 48 (by decide +kernel) (by decide +kernel)
    f4_diag_r240_n16
    (f4_range_join 256 16 272 16 32 (by decide +kernel) (by decide +kernel)
    f4_diag_r256_n16
    f4_diag_r272_n16))
    (f4_range_join 288 16 304 21 37 (by decide +kernel) (by decide +kernel)
    f4_diag_r288_n16
    (f4_range_join 304 16 320 5 21 (by decide +kernel) (by decide +kernel)
    f4_diag_r304_n16
    f4_diag_r320_n05)))))

end VOA.DeligneAudit.DeligneSector.F4
