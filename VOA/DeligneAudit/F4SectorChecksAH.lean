/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksStabG11R246N16
import VOA.DeligneAudit.F4SectorChecksStabG11R262N16
import VOA.DeligneAudit.F4SectorChecksStabG11R278N16
import VOA.DeligneAudit.F4SectorChecksStabG11R294N16
import VOA.DeligneAudit.F4SectorChecksStabG11R310N15
import VOA.DeligneAudit.F4SectorChecksWeightRow00
import VOA.DeligneAudit.F4SectorChecksWeightRow01
import VOA.DeligneAudit.F4SectorChecksWeightRow02
import VOA.DeligneAudit.F4SectorChecksWeightRow03
import VOA.DeligneAudit.F4SectorChecksWeightRow04
import VOA.DeligneAudit.F4SectorChecksWeightRow05
import VOA.DeligneAudit.F4SectorChecksWeightRow06
import VOA.DeligneAudit.F4SectorChecksWeightRow07
import VOA.DeligneAudit.F4SectorChecksWeightRow08
import VOA.DeligneAudit.F4SectorChecksWeightRow09
import VOA.DeligneAudit.F4SectorChecksWeightRow10
import VOA.DeligneAudit.F4SectorChecksWeightRow11
import VOA.DeligneAudit.F4SectorChecksWeightRow12
import VOA.DeligneAudit.F4SectorChecksWeightRow13
import VOA.DeligneAudit.F4SectorChecksWeightRow14
import VOA.DeligneAudit.F4SectorChecksWeightRow15
import VOA.DeligneAudit.F4SectorChecksWeightRow16
import VOA.DeligneAudit.F4SectorChecksWeightRow17
import VOA.DeligneAudit.F4SectorChecksWeightRow18
import VOA.DeligneAudit.F4SectorChecksWeightRow19
import VOA.DeligneAudit.F4SectorChecksWeightRow20
import VOA.DeligneAudit.F4SectorChecksWeightRow21
import VOA.DeligneAudit.F4SectorChecksWeightRow22
import VOA.DeligneAudit.F4SectorChecksWeightRow23
import VOA.DeligneAudit.F4SectorChecksWeightRow24
import VOA.DeligneAudit.F4SectorChecksWeightRow25

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem stab_b11_246 : (List.range' 246 79).all (stabCheck 11) = true := by
  exact (f4_range_join 246 32 278 47 79 (by decide +kernel) (by decide +kernel)
    (f4_range_join 246 16 262 16 32 (by decide +kernel) (by decide +kernel)
    f4_stab_g11_r246_n16
    f4_stab_g11_r262_n16)
    (f4_range_join 278 16 294 31 47 (by decide +kernel) (by decide +kernel)
    f4_stab_g11_r278_n16
    (f4_range_join 294 16 310 15 31 (by decide +kernel) (by decide +kernel)
    f4_stab_g11_r294_n16
    f4_stab_g11_r310_n15)))

theorem wt_b0 :
    (List.range' 0 13).all (fun a => (List.range 52).all fun b => (br a b).all fun p =>
    (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) = true := by
  exact (f4_range_join 0 6 6 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 3 3 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 1 1 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_00
    (f4_range_join 1 1 2 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_01
    f4_weight_row_02))
    (f4_range_join 3 1 4 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_03
    (f4_range_join 4 1 5 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_04
    f4_weight_row_05)))
    (f4_range_join 6 3 9 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 6 1 7 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_06
    (f4_range_join 7 1 8 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_07
    f4_weight_row_08))
    (f4_range_join 9 2 11 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 9 1 10 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_09
    f4_weight_row_10)
    (f4_range_join 11 1 12 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_11
    f4_weight_row_12))))

theorem wt_b13 :
    (List.range' 13 13).all (fun a => (List.range 52).all fun b => (br a b).all fun p =>
    (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) = true := by
  exact (f4_range_join 13 6 19 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 13 3 16 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 13 1 14 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_13
    (f4_range_join 14 1 15 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_14
    f4_weight_row_15))
    (f4_range_join 16 1 17 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_16
    (f4_range_join 17 1 18 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_17
    f4_weight_row_18)))
    (f4_range_join 19 3 22 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 19 1 20 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_19
    (f4_range_join 20 1 21 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_20
    f4_weight_row_21))
    (f4_range_join 22 2 24 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 22 1 23 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_22
    f4_weight_row_23)
    (f4_range_join 24 1 25 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_24
    f4_weight_row_25))))


end VOA.DeligneAudit.DeligneSector.F4
