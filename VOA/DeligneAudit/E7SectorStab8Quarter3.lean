/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData8
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 8 stability rows[1155,1540), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab8_rows_1155_1210 : stabPart 8 stab8 1155 1210 = true := by
  decide +kernel

theorem stab8_rows_1210_1265 : stabPart 8 stab8 1210 1265 = true := by
  decide +kernel

theorem stab8_rows_1265_1320 : stabPart 8 stab8 1265 1320 = true := by
  decide +kernel

theorem stab8_rows_1320_1375 : stabPart 8 stab8 1320 1375 = true := by
  decide +kernel

theorem stab8_rows_1375_1430 : stabPart 8 stab8 1375 1430 = true := by
  decide +kernel

theorem stab8_rows_1430_1485 : stabPart 8 stab8 1430 1485 = true := by
  decide +kernel

theorem stab8_rows_1485_1540 : stabPart 8 stab8 1485 1540 = true := by
  decide +kernel

theorem stab8_quarter3 : stabPart 8 stab8 1155 1540 = true :=
  (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1155_1210
    (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1210_1265
      (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1265_1320
        (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1320_1375
          (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1375_1430
            (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_1430_1485
              stab8_rows_1485_1540))))))

#print axioms stab8_quarter3
end VOA.DeligneAudit.DeligneCarrier.E7
