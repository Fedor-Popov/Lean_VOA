/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData10
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 10 stability rows[0,385), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab10_rows_0_55 : stabPart 10 stab10 0 55 = true := by
  decide +kernel

theorem stab10_rows_55_110 : stabPart 10 stab10 55 110 = true := by
  decide +kernel

theorem stab10_rows_110_165 : stabPart 10 stab10 110 165 = true := by
  decide +kernel

theorem stab10_rows_165_220 : stabPart 10 stab10 165 220 = true := by
  decide +kernel

theorem stab10_rows_220_275 : stabPart 10 stab10 220 275 = true := by
  decide +kernel

theorem stab10_rows_275_330 : stabPart 10 stab10 275 330 = true := by
  decide +kernel

theorem stab10_rows_330_385 : stabPart 10 stab10 330 385 = true := by
  decide +kernel

theorem stab10_quarter0 : stabPart 10 stab10 0 385 = true :=
  (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_0_55
    (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_55_110
      (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_110_165
        (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_165_220
          (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_220_275
            (stabPart_join 10 stab10 (by decide) (by decide) stab10_rows_275_330
              stab10_rows_330_385))))))

#print axioms stab10_quarter0
end VOA.DeligneAudit.DeligneCarrier.E7
