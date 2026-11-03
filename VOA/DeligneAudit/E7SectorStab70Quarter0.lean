/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData70
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 70 stability rows[0,385), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab70_rows_0_55 : stabPart 70 stab70 0 55 = true := by
  decide +kernel

theorem stab70_rows_55_110 : stabPart 70 stab70 55 110 = true := by
  decide +kernel

theorem stab70_rows_110_165 : stabPart 70 stab70 110 165 = true := by
  decide +kernel

theorem stab70_rows_165_220 : stabPart 70 stab70 165 220 = true := by
  decide +kernel

theorem stab70_rows_220_275 : stabPart 70 stab70 220 275 = true := by
  decide +kernel

theorem stab70_rows_275_330 : stabPart 70 stab70 275 330 = true := by
  decide +kernel

theorem stab70_rows_330_385 : stabPart 70 stab70 330 385 = true := by
  decide +kernel

theorem stab70_quarter0 : stabPart 70 stab70 0 385 = true :=
  (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_0_55
    (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_55_110
      (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_110_165
        (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_165_220
          (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_220_275
            (stabPart_join 70 stab70 (by decide) (by decide) stab70_rows_275_330
              stab70_rows_330_385))))))

#print axioms stab70_quarter0
end VOA.DeligneAudit.DeligneCarrier.E7
