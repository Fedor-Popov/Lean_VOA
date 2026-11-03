/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData13
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 13 stability rows[0,385), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab13_rows_0_55 : stabPart 13 stab13 0 55 = true := by
  decide +kernel

theorem stab13_rows_55_110 : stabPart 13 stab13 55 110 = true := by
  decide +kernel

theorem stab13_rows_110_165 : stabPart 13 stab13 110 165 = true := by
  decide +kernel

theorem stab13_rows_165_220 : stabPart 13 stab13 165 220 = true := by
  decide +kernel

theorem stab13_rows_220_275 : stabPart 13 stab13 220 275 = true := by
  decide +kernel

theorem stab13_rows_275_330 : stabPart 13 stab13 275 330 = true := by
  decide +kernel

theorem stab13_rows_330_385 : stabPart 13 stab13 330 385 = true := by
  decide +kernel

theorem stab13_quarter0 : stabPart 13 stab13 0 385 = true :=
  (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_0_55
    (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_55_110
      (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_110_165
        (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_165_220
          (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_220_275
            (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_275_330
              stab13_rows_330_385))))))

#print axioms stab13_quarter0
end VOA.DeligneAudit.DeligneCarrier.E7
