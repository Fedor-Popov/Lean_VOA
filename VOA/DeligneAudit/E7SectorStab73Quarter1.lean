/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorStabData73
import VOA.DeligneAudit.E7SectorStabilityJoin

/-! Exact E7 generator 73 stability rows[385,770), checked in small leaves.
The final range fact joins opaque checked facts without a full-range kernel evaluation. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

theorem stab73_rows_385_440 : stabPart 73 stab73 385 440 = true := by
  decide +kernel

theorem stab73_rows_440_495 : stabPart 73 stab73 440 495 = true := by
  decide +kernel

theorem stab73_rows_495_550 : stabPart 73 stab73 495 550 = true := by
  decide +kernel

theorem stab73_rows_550_605 : stabPart 73 stab73 550 605 = true := by
  decide +kernel

theorem stab73_rows_605_660 : stabPart 73 stab73 605 660 = true := by
  decide +kernel

theorem stab73_rows_660_715 : stabPart 73 stab73 660 715 = true := by
  decide +kernel

theorem stab73_rows_715_770 : stabPart 73 stab73 715 770 = true := by
  decide +kernel

theorem stab73_quarter1 : stabPart 73 stab73 385 770 = true :=
  (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_385_440
    (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_440_495
      (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_495_550
        (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_550_605
          (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_605_660
            (stabPart_join 73 stab73 (by decide) (by decide) stab73_rows_660_715
              stab73_rows_715_770))))))

#print axioms stab73_quarter1
end VOA.DeligneAudit.DeligneCarrier.E7
