/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym046
import VOA.DeligneAudit.DeligneDivisorD4CheckSym047
import VOA.DeligneAudit.DeligneDivisorD4CheckSym048
import VOA.DeligneAudit.DeligneDivisorD4CheckSym049
import VOA.DeligneAudit.DeligneDivisorD4CheckSym050
import VOA.DeligneAudit.DeligneDivisorD4CheckSym051

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_7 :
    (List.range' 0 7).all (fun d => !decide (7 ≤ d) || symCheck 7 d) = true := by
  decide +kernel

theorem d4_small_075 : symChecks 7 8 = true := by
  apply symChecks_row_of_range 7 8 (by decide)
  exact check_range_join 0 7 7 21 28 (by decide) (by decide) d4_sym_prefix_7
    (check_range_join 7 4 11 17 21 (by decide) (by decide) d4_sym_pairs_046
    (check_range_join 11 4 15 13 17 (by decide) (by decide) d4_sym_pairs_047
    (check_range_join 15 4 19 9 13 (by decide) (by decide) d4_sym_pairs_048
    (check_range_join 19 4 23 5 9 (by decide) (by decide) d4_sym_pairs_049
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_050
    (d4_sym_pairs_051))))))

end VOA.DeligneAudit.DeligneDivisor.D4
