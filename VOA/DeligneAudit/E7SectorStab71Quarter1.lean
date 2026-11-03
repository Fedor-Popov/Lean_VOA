/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData71
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 71 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab71_rows_385_440 : stabPart 71 stab71 385 440 = true := by
  decide +kernel

theorem stab71_rows_440_495 : stabPart 71 stab71 440 495 = true := by
  decide +kernel

theorem stab71_rows_495_550 : stabPart 71 stab71 495 550 = true := by
  decide +kernel

theorem stab71_rows_550_605 : stabPart 71 stab71 550 605 = true := by
  decide +kernel

theorem stab71_rows_605_660 : stabPart 71 stab71 605 660 = true := by
  decide +kernel

theorem stab71_rows_660_715 : stabPart 71 stab71 660 715 = true := by
  decide +kernel

theorem stab71_rows_715_770 : stabPart 71 stab71 715 770 = true := by
  decide +kernel

theorem stab71_quarter1 : stabPart 71 stab71 385 770 = true :=
  (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_385_440
    (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_440_495
      (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_495_550
        (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_550_605
          (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_605_660
            (stabPart_join 71 stab71 (by decide) (by decide) stab71_rows_660_715
              stab71_rows_715_770))))))

#print axioms stab71_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
