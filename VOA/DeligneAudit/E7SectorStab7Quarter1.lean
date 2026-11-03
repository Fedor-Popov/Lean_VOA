/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData7
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 7 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab7_rows_385_440 : stabPart 7 stab7 385 440 = true := by
  decide +kernel

theorem stab7_rows_440_495 : stabPart 7 stab7 440 495 = true := by
  decide +kernel

theorem stab7_rows_495_550 : stabPart 7 stab7 495 550 = true := by
  decide +kernel

theorem stab7_rows_550_605 : stabPart 7 stab7 550 605 = true := by
  decide +kernel

theorem stab7_rows_605_660 : stabPart 7 stab7 605 660 = true := by
  decide +kernel

theorem stab7_rows_660_715 : stabPart 7 stab7 660 715 = true := by
  decide +kernel

theorem stab7_rows_715_770 : stabPart 7 stab7 715 770 = true := by
  decide +kernel

theorem stab7_quarter1 : stabPart 7 stab7 385 770 = true :=
  (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_385_440
    (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_440_495
      (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_495_550
        (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_550_605
          (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_605_660
            (stabPart_join 7 stab7 (by decide) (by decide) stab7_rows_660_715
              stab7_rows_715_770))))))

#print axioms stab7_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
