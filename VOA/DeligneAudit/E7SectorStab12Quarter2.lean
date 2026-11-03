/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData12
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 12 stability rows[770,1155), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab12_rows_770_825 : stabPart 12 stab12 770 825 = true := by
  decide +kernel

theorem stab12_rows_825_880 : stabPart 12 stab12 825 880 = true := by
  decide +kernel

theorem stab12_rows_880_935 : stabPart 12 stab12 880 935 = true := by
  decide +kernel

theorem stab12_rows_935_990 : stabPart 12 stab12 935 990 = true := by
  decide +kernel

theorem stab12_rows_990_1045 : stabPart 12 stab12 990 1045 = true := by
  decide +kernel

theorem stab12_rows_1045_1100 : stabPart 12 stab12 1045 1100 = true := by
  decide +kernel

theorem stab12_rows_1100_1155 : stabPart 12 stab12 1100 1155 = true := by
  decide +kernel

theorem stab12_quarter2 : stabPart 12 stab12 770 1155 = true :=
  (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_770_825
    (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_825_880
      (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_880_935
        (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_935_990
          (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_990_1045
            (stabPart_join 12 stab12 (by decide) (by decide) stab12_rows_1045_1100
              stab12_rows_1100_1155))))))

#print axioms stab12_quarter2
end VOA.DeligneAudit.DeligneCarrier.E7
