/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym040
import VOA.DeligneAudit.DeligneDivisorD4CheckSym041
import VOA.DeligneAudit.DeligneDivisorD4CheckSym042
import VOA.DeligneAudit.DeligneDivisorD4CheckSym043
import VOA.DeligneAudit.DeligneDivisorD4CheckSym044
import VOA.DeligneAudit.DeligneDivisorD4CheckSym045

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_6 :
    (List.range' 0 6).all (fun d => !decide (6 ≤ d) || symCheck 6 d) = true := by
  decide +kernel

theorem d4_small_074 : symChecks 6 7 = true := by
  apply symChecks_row_of_range 6 7 (by decide)
  exact check_range_join 0 6 6 22 28 (by decide) (by decide) d4_sym_prefix_6
    (check_range_join 6 4 10 18 22 (by decide) (by decide) d4_sym_pairs_040
    (check_range_join 10 4 14 14 18 (by decide) (by decide) d4_sym_pairs_041
    (check_range_join 14 4 18 10 14 (by decide) (by decide) d4_sym_pairs_042
    (check_range_join 18 4 22 6 10 (by decide) (by decide) d4_sym_pairs_043
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_044
    (d4_sym_pairs_045))))))

end VOA.DeligneAudit.DeligneDivisor.D4
