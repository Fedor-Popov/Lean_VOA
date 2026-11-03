/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData8
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 8 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab8_rows_385_440 : stabPart 8 stab8 385 440 = true := by
  decide +kernel

theorem stab8_rows_440_495 : stabPart 8 stab8 440 495 = true := by
  decide +kernel

theorem stab8_rows_495_550 : stabPart 8 stab8 495 550 = true := by
  decide +kernel

theorem stab8_rows_550_605 : stabPart 8 stab8 550 605 = true := by
  decide +kernel

theorem stab8_rows_605_660 : stabPart 8 stab8 605 660 = true := by
  decide +kernel

theorem stab8_rows_660_715 : stabPart 8 stab8 660 715 = true := by
  decide +kernel

theorem stab8_rows_715_770 : stabPart 8 stab8 715 770 = true := by
  decide +kernel

theorem stab8_quarter1 : stabPart 8 stab8 385 770 = true :=
  (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_385_440
    (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_440_495
      (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_495_550
        (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_550_605
          (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_605_660
            (stabPart_join 8 stab8 (by decide) (by decide) stab8_rows_660_715
              stab8_rows_715_770))))))

#print axioms stab8_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
