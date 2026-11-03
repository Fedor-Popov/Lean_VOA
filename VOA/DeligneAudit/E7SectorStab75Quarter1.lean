/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData75
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 75 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab75_rows_385_440 : stabPart 75 stab75 385 440 = true := by
  decide +kernel

theorem stab75_rows_440_495 : stabPart 75 stab75 440 495 = true := by
  decide +kernel

theorem stab75_rows_495_550 : stabPart 75 stab75 495 550 = true := by
  decide +kernel

theorem stab75_rows_550_605 : stabPart 75 stab75 550 605 = true := by
  decide +kernel

theorem stab75_rows_605_660 : stabPart 75 stab75 605 660 = true := by
  decide +kernel

theorem stab75_rows_660_715 : stabPart 75 stab75 660 715 = true := by
  decide +kernel

theorem stab75_rows_715_770 : stabPart 75 stab75 715 770 = true := by
  decide +kernel

theorem stab75_quarter1 : stabPart 75 stab75 385 770 = true :=
  (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_385_440
    (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_440_495
      (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_495_550
        (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_550_605
          (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_605_660
            (stabPart_join 75 stab75 (by decide) (by decide) stab75_rows_660_715
              stab75_rows_715_770))))))

#print axioms stab75_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
