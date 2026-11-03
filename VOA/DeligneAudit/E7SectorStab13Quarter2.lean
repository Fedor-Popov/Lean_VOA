/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData13
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 13 stability rows[770,1155), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab13_rows_770_825 : stabPart 13 stab13 770 825 = true := by
  decide +kernel

theorem stab13_rows_825_880 : stabPart 13 stab13 825 880 = true := by
  decide +kernel

theorem stab13_rows_880_935 : stabPart 13 stab13 880 935 = true := by
  decide +kernel

theorem stab13_rows_935_990 : stabPart 13 stab13 935 990 = true := by
  decide +kernel

theorem stab13_rows_990_1045 : stabPart 13 stab13 990 1045 = true := by
  decide +kernel

theorem stab13_rows_1045_1100 : stabPart 13 stab13 1045 1100 = true := by
  decide +kernel

theorem stab13_rows_1100_1155 : stabPart 13 stab13 1100 1155 = true := by
  decide +kernel

theorem stab13_quarter2 : stabPart 13 stab13 770 1155 = true :=
  (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_770_825
    (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_825_880
      (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_880_935
        (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_935_990
          (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_990_1045
            (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_1045_1100
              stab13_rows_1100_1155))))))

#print axioms stab13_quarter2
end VOA.DeligneAudit.DeligneCarrier.E7
