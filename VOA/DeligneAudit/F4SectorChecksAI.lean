/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4SectorChecksWeightRow26
import VOA.DeligneAudit.F4SectorChecksWeightRow27
import VOA.DeligneAudit.F4SectorChecksWeightRow28
import VOA.DeligneAudit.F4SectorChecksWeightRow29
import VOA.DeligneAudit.F4SectorChecksWeightRow30
import VOA.DeligneAudit.F4SectorChecksWeightRow31
import VOA.DeligneAudit.F4SectorChecksWeightRow32
import VOA.DeligneAudit.F4SectorChecksWeightRow33
import VOA.DeligneAudit.F4SectorChecksWeightRow34
import VOA.DeligneAudit.F4SectorChecksWeightRow35
import VOA.DeligneAudit.F4SectorChecksWeightRow36
import VOA.DeligneAudit.F4SectorChecksWeightRow37
import VOA.DeligneAudit.F4SectorChecksWeightRow38
import VOA.DeligneAudit.F4SectorChecksWeightRow39
import VOA.DeligneAudit.F4SectorChecksWeightRow40
import VOA.DeligneAudit.F4SectorChecksWeightRow41
import VOA.DeligneAudit.F4SectorChecksWeightRow42
import VOA.DeligneAudit.F4SectorChecksWeightRow43
import VOA.DeligneAudit.F4SectorChecksWeightRow44
import VOA.DeligneAudit.F4SectorChecksWeightRow45
import VOA.DeligneAudit.F4SectorChecksWeightRow46
import VOA.DeligneAudit.F4SectorChecksWeightRow47
import VOA.DeligneAudit.F4SectorChecksWeightRow48
import VOA.DeligneAudit.F4SectorChecksWeightRow49
import VOA.DeligneAudit.F4SectorChecksWeightRow50
import VOA.DeligneAudit.F4SectorChecksWeightRow51
import VOA.DeligneAudit.F4SectorChecksRelRangeR000N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR016N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR032N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR048N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR064N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR080N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR096N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR112N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR128N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR144N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR160N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR176N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR192N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR208N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR224N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR240N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR256N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR272N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR288N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR304N16
import VOA.DeligneAudit.F4SectorChecksRelRangeR320N05

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem wt_b26 :
    (List.range' 26 13).all (fun a => (List.range 52).all fun b => (br a b).all fun p =>
    (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) = true := by
  exact (f4_range_join 26 6 32 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 26 3 29 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 26 1 27 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_26
    (f4_range_join 27 1 28 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_27
    f4_weight_row_28))
    (f4_range_join 29 1 30 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_29
    (f4_range_join 30 1 31 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_30
    f4_weight_row_31)))
    (f4_range_join 32 3 35 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 32 1 33 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_32
    (f4_range_join 33 1 34 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_33
    f4_weight_row_34))
    (f4_range_join 35 2 37 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 35 1 36 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_35
    f4_weight_row_36)
    (f4_range_join 37 1 38 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_37
    f4_weight_row_38))))

theorem wt_b39 :
    (List.range' 39 13).all (fun a => (List.range 52).all fun b => (br a b).all fun p =>
    (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) = true := by
  exact (f4_range_join 39 6 45 7 13 (by decide +kernel) (by decide +kernel)
    (f4_range_join 39 3 42 3 6 (by decide +kernel) (by decide +kernel)
    (f4_range_join 39 1 40 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_39
    (f4_range_join 40 1 41 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_40
    f4_weight_row_41))
    (f4_range_join 42 1 43 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_42
    (f4_range_join 43 1 44 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_43
    f4_weight_row_44)))
    (f4_range_join 45 3 48 4 7 (by decide +kernel) (by decide +kernel)
    (f4_range_join 45 1 46 2 3 (by decide +kernel) (by decide +kernel)
    f4_weight_row_45
    (f4_range_join 46 1 47 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_46
    f4_weight_row_47))
    (f4_range_join 48 2 50 2 4 (by decide +kernel) (by decide +kernel)
    (f4_range_join 48 1 49 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_48
    f4_weight_row_49)
    (f4_range_join 50 1 51 1 2 (by decide +kernel) (by decide +kernel)
    f4_weight_row_50
    f4_weight_row_51))))

theorem relRange_ok : relRange = true := by
  exact f4_relRange_of_rows
    (f4_range_join 0 160 160 165 325 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 80 80 80 160 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 32 32 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 16 16 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r000_n16
    f4_relrange_r016_n16)
    (f4_range_join 32 16 48 32 48 (by decide +kernel) (by decide +kernel)
    f4_relrange_r032_n16
    (f4_range_join 48 16 64 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r048_n16
    f4_relrange_r064_n16)))
    (f4_range_join 80 32 112 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 80 16 96 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r080_n16
    f4_relrange_r096_n16)
    (f4_range_join 112 16 128 32 48 (by decide +kernel) (by decide +kernel)
    f4_relrange_r112_n16
    (f4_range_join 128 16 144 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r128_n16
    f4_relrange_r144_n16))))
    (f4_range_join 160 80 240 85 165 (by decide +kernel) (by decide +kernel)
    (f4_range_join 160 32 192 48 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 160 16 176 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r160_n16
    f4_relrange_r176_n16)
    (f4_range_join 192 16 208 32 48 (by decide +kernel) (by decide +kernel)
    f4_relrange_r192_n16
    (f4_range_join 208 16 224 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r208_n16
    f4_relrange_r224_n16)))
    (f4_range_join 240 48 288 37 85 (by decide +kernel) (by decide +kernel)
    (f4_range_join 240 16 256 32 48 (by decide +kernel) (by decide +kernel)
    f4_relrange_r240_n16
    (f4_range_join 256 16 272 16 32 (by decide +kernel) (by decide +kernel)
    f4_relrange_r256_n16
    f4_relrange_r272_n16))
    (f4_range_join 288 16 304 21 37 (by decide +kernel) (by decide +kernel)
    f4_relrange_r288_n16
    (f4_range_join 304 16 320 5 21 (by decide +kernel) (by decide +kernel)
    f4_relrange_r304_n16
    f4_relrange_r320_n05)))))


end VOA.DeligneAudit.DeligneSector.F4
