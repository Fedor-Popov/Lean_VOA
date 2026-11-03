/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym021
import VOA.DeligneAudit.DeligneDivisorD4CheckSym022
import VOA.DeligneAudit.DeligneDivisorD4CheckSym023
import VOA.DeligneAudit.DeligneDivisorD4CheckSym024
import VOA.DeligneAudit.DeligneDivisorD4CheckSym025
import VOA.DeligneAudit.DeligneDivisorD4CheckSym026
import VOA.DeligneAudit.DeligneDivisorD4CheckSym027

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_3 :
    (List.range' 0 3).all (fun d => !decide (3 ≤ d) || symCheck 3 d) = true := by
  decide +kernel

theorem d4_small_071 : symChecks 3 4 = true := by
  apply symChecks_row_of_range 3 4 (by decide)
  exact check_range_join 0 3 3 25 28 (by decide) (by decide) d4_sym_prefix_3
    (check_range_join 3 4 7 21 25 (by decide) (by decide) d4_sym_pairs_021
    (check_range_join 7 4 11 17 21 (by decide) (by decide) d4_sym_pairs_022
    (check_range_join 11 4 15 13 17 (by decide) (by decide) d4_sym_pairs_023
    (check_range_join 15 4 19 9 13 (by decide) (by decide) d4_sym_pairs_024
    (check_range_join 19 4 23 5 9 (by decide) (by decide) d4_sym_pairs_025
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_026
    (d4_sym_pairs_027)))))))

end VOA.DeligneAudit.DeligneDivisor.D4
