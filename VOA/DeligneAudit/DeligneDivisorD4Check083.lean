/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym084
import VOA.DeligneAudit.DeligneDivisorD4CheckSym085
import VOA.DeligneAudit.DeligneDivisorD4CheckSym086
import VOA.DeligneAudit.DeligneDivisorD4CheckSym087

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_15 :
    (List.range' 0 15).all (fun d => !decide (15 ≤ d) || symCheck 15 d) = true := by
  decide +kernel

theorem d4_small_083 : symChecks 15 16 = true := by
  apply symChecks_row_of_range 15 16 (by decide)
  exact check_range_join 0 15 15 13 28 (by decide) (by decide) d4_sym_prefix_15
    (check_range_join 15 4 19 9 13 (by decide) (by decide) d4_sym_pairs_084
    (check_range_join 19 4 23 5 9 (by decide) (by decide) d4_sym_pairs_085
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_086
    (d4_sym_pairs_087))))

end VOA.DeligneAudit.DeligneDivisor.D4
