/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData9
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 9 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab9_rows_385_440 : stabPart 9 stab9 385 440 = true := by
  decide +kernel

theorem stab9_rows_440_495 : stabPart 9 stab9 440 495 = true := by
  decide +kernel

theorem stab9_rows_495_550 : stabPart 9 stab9 495 550 = true := by
  decide +kernel

theorem stab9_rows_550_605 : stabPart 9 stab9 550 605 = true := by
  decide +kernel

theorem stab9_rows_605_660 : stabPart 9 stab9 605 660 = true := by
  decide +kernel

theorem stab9_rows_660_715 : stabPart 9 stab9 660 715 = true := by
  decide +kernel

theorem stab9_rows_715_770 : stabPart 9 stab9 715 770 = true := by
  decide +kernel

theorem stab9_quarter1 : stabPart 9 stab9 385 770 = true :=
  (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_385_440
    (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_440_495
      (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_495_550
        (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_550_605
          (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_605_660
            (stabPart_join 9 stab9 (by decide) (by decide) stab9_rows_660_715
              stab9_rows_715_770))))))

#print axioms stab9_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
