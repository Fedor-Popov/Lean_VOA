/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData8
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 8 stability rows[0,385), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab8_rows_0_55 : stabPart 8 stab8 0 55 = true := by
  decide +kernel

theorem stab8_rows_55_110 : stabPart 8 stab8 55 110 = true := by
  decide +kernel

theorem stab8_rows_110_165 : stabPart 8 stab8 110 165 = true := by
  decide +kernel

theorem stab8_rows_165_220 : stabPart 8 stab8 165 220 = true := by
  decide +kernel

theorem stab8_rows_220_275 : stabPart 8 stab8 220 275 = true := by
  decide +kernel

theorem stab8_rows_275_330 : stabPart 8 stab8 275 330 = true := by
  decide +kernel

theorem stab8_rows_330_385 : stabPart 8 stab8 330 385 = true := by
  decide +kernel

theorem stab8_quarter0 : stabPart 8 stab8 0 385 = true :=
  (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_0_55
    (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_55_110
      (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_110_165
        (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_165_220
          (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_220_275
            (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_275_330
              stab8_rows_330_385))))))

#print axioms stab8_quarter0
end VOA.DeligneAudit.DeligneCarrier.E7
