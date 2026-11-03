/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData7
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 7 stability rows[770,1155), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab7_rows_770_825 : stabPart 7 stab7 770 825 = true := by
  decide +kernel

theorem stab7_rows_825_880 : stabPart 7 stab7 825 880 = true := by
  decide +kernel

theorem stab7_rows_880_935 : stabPart 7 stab7 880 935 = true := by
  decide +kernel

theorem stab7_rows_935_990 : stabPart 7 stab7 935 990 = true := by
  decide +kernel

theorem stab7_rows_990_1045 : stabPart 7 stab7 990 1045 = true := by
  decide +kernel

theorem stab7_rows_1045_1100 : stabPart 7 stab7 1045 1100 = true := by
  decide +kernel

theorem stab7_rows_1100_1155 : stabPart 7 stab7 1100 1155 = true := by
  decide +kernel

theorem stab7_quarter2 : stabPart 7 stab7 770 1155 = true :=
  (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_770_825
    (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_825_880
      (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_880_935
        (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_935_990
          (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_990_1045
            (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_1045_1100
              stab7_rows_1100_1155))))))

#print axioms stab7_quarter2
end VOA.DeligneAudit.DeligneCarrier.E7
