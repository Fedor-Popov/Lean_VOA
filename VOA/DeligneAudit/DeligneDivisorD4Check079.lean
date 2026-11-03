/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym067
import VOA.DeligneAudit.DeligneDivisorD4CheckSym068
import VOA.DeligneAudit.DeligneDivisorD4CheckSym069
import VOA.DeligneAudit.DeligneDivisorD4CheckSym070
import VOA.DeligneAudit.DeligneDivisorD4CheckSym071

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_11 :
    (List.range' 0 11).all (fun d => !decide (11 ≤ d) || symCheck 11 d) = true := by
  decide +kernel

theorem d4_small_079 : symChecks 11 12 = true := by
  apply symChecks_row_of_range 11 12 (by decide)
  exact check_range_join 0 11 11 17 28 (by decide) (by decide) d4_sym_prefix_11
    (check_range_join 11 4 15 13 17 (by decide) (by decide) d4_sym_pairs_067
    (check_range_join 15 4 19 9 13 (by decide) (by decide) d4_sym_pairs_068
    (check_range_join 19 4 23 5 9 (by decide) (by decide) d4_sym_pairs_069
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_070
    (d4_sym_pairs_071)))))

end VOA.DeligneAudit.DeligneDivisor.D4
