/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym034
import VOA.DeligneAudit.DeligneDivisorD4CheckSym035
import VOA.DeligneAudit.DeligneDivisorD4CheckSym036
import VOA.DeligneAudit.DeligneDivisorD4CheckSym037
import VOA.DeligneAudit.DeligneDivisorD4CheckSym038
import VOA.DeligneAudit.DeligneDivisorD4CheckSym039

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_5 :
    (List.range' 0 5).all (fun d => !decide (5 ≤ d) || symCheck 5 d) = true := by
  decide +kernel

theorem d4_small_073 : symChecks 5 6 = true := by
  apply symChecks_row_of_range 5 6 (by decide)
  exact check_range_join 0 5 5 23 28 (by decide) (by decide) d4_sym_prefix_5
    (check_range_join 5 4 9 19 23 (by decide) (by decide) d4_sym_pairs_034
    (check_range_join 9 4 13 15 19 (by decide) (by decide) d4_sym_pairs_035
    (check_range_join 13 4 17 11 15 (by decide) (by decide) d4_sym_pairs_036
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_sym_pairs_037
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_038
    (d4_sym_pairs_039))))))

end VOA.DeligneAudit.DeligneDivisor.D4
