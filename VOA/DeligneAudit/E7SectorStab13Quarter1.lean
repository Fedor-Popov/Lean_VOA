/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData13
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 13 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab13_rows_385_440 : stabPart 13 stab13 385 440 = true := by
  decide +kernel

theorem stab13_rows_440_495 : stabPart 13 stab13 440 495 = true := by
  decide +kernel

theorem stab13_rows_495_550 : stabPart 13 stab13 495 550 = true := by
  decide +kernel

theorem stab13_rows_550_605 : stabPart 13 stab13 550 605 = true := by
  decide +kernel

theorem stab13_rows_605_660 : stabPart 13 stab13 605 660 = true := by
  decide +kernel

theorem stab13_rows_660_715 : stabPart 13 stab13 660 715 = true := by
  decide +kernel

theorem stab13_rows_715_770 : stabPart 13 stab13 715 770 = true := by
  decide +kernel

theorem stab13_quarter1 : stabPart 13 stab13 385 770 = true :=
  (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_385_440
    (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_440_495
      (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_495_550
        (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_550_605
          (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_605_660
            (stabPart_join 13 stab13 (by decide) (by decide) stab13_rows_660_715
              stab13_rows_715_770))))))

#print axioms stab13_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
