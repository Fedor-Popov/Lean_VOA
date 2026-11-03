/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData76
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 76 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab76_rows_385_440 : stabPart 76 stab76 385 440 = true := by
  decide +kernel

theorem stab76_rows_440_495 : stabPart 76 stab76 440 495 = true := by
  decide +kernel

theorem stab76_rows_495_550 : stabPart 76 stab76 495 550 = true := by
  decide +kernel

theorem stab76_rows_550_605 : stabPart 76 stab76 550 605 = true := by
  decide +kernel

theorem stab76_rows_605_660 : stabPart 76 stab76 605 660 = true := by
  decide +kernel

theorem stab76_rows_660_715 : stabPart 76 stab76 660 715 = true := by
  decide +kernel

theorem stab76_rows_715_770 : stabPart 76 stab76 715 770 = true := by
  decide +kernel

theorem stab76_quarter1 : stabPart 76 stab76 385 770 = true :=
  (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_385_440
    (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_440_495
      (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_495_550
        (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_550_605
          (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_605_660
            (stabPart_join 76 stab76 (by decide) (by decide) stab76_rows_660_715
              stab76_rows_715_770))))))

#print axioms stab76_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
