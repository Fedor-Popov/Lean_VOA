/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym007
import VOA.DeligneAudit.DeligneDivisorD4CheckSym008
import VOA.DeligneAudit.DeligneDivisorD4CheckSym009
import VOA.DeligneAudit.DeligneDivisorD4CheckSym010
import VOA.DeligneAudit.DeligneDivisorD4CheckSym011
import VOA.DeligneAudit.DeligneDivisorD4CheckSym012
import VOA.DeligneAudit.DeligneDivisorD4CheckSym013

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_1 :
    (List.range' 0 1).all (fun d => !decide (1 ≤ d) || symCheck 1 d) = true := by
  decide +kernel

theorem d4_small_069 : symChecks 1 2 = true := by
  apply symChecks_row_of_range 1 2 (by decide)
  exact check_range_join 0 1 1 27 28 (by decide) (by decide) d4_sym_prefix_1
    (check_range_join 1 4 5 23 27 (by decide) (by decide) d4_sym_pairs_007
    (check_range_join 5 4 9 19 23 (by decide) (by decide) d4_sym_pairs_008
    (check_range_join 9 4 13 15 19 (by decide) (by decide) d4_sym_pairs_009
    (check_range_join 13 4 17 11 15 (by decide) (by decide) d4_sym_pairs_010
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_sym_pairs_011
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_012
    (d4_sym_pairs_013)))))))

end VOA.DeligneAudit.DeligneDivisor.D4
