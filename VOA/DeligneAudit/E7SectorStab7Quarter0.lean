/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData7
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 7 stability rows[0,385), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab7_rows_0_55 : stabPart 7 stab7 0 55 = true := by
  decide +kernel

theorem stab7_rows_55_110 : stabPart 7 stab7 55 110 = true := by
  decide +kernel

theorem stab7_rows_110_165 : stabPart 7 stab7 110 165 = true := by
  decide +kernel

theorem stab7_rows_165_220 : stabPart 7 stab7 165 220 = true := by
  decide +kernel

theorem stab7_rows_220_275 : stabPart 7 stab7 220 275 = true := by
  decide +kernel

theorem stab7_rows_275_330 : stabPart 7 stab7 275 330 = true := by
  decide +kernel

theorem stab7_rows_330_385 : stabPart 7 stab7 330 385 = true := by
  decide +kernel

theorem stab7_quarter0 : stabPart 7 stab7 0 385 = true :=
  (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_0_55
    (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_55_110
      (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_110_165
        (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_165_220
          (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_220_275
            (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_275_330
              stab7_rows_330_385))))))

#print axioms stab7_quarter0
end VOA.DeligneAudit.DeligneCarrier.E7
