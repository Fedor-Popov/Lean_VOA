/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym076
import VOA.DeligneAudit.DeligneDivisorD4CheckSym077
import VOA.DeligneAudit.DeligneDivisorD4CheckSym078
import VOA.DeligneAudit.DeligneDivisorD4CheckSym079

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_13 :
    (List.range' 0 13).all (fun d => !decide (13 ≤ d) || symCheck 13 d) = true := by
  decide +kernel

theorem d4_small_081 : symChecks 13 14 = true := by
  apply symChecks_row_of_range 13 14 (by decide)
  exact check_range_join 0 13 13 15 28 (by decide) (by decide) d4_sym_prefix_13
    (check_range_join 13 4 17 11 15 (by decide) (by decide) d4_sym_pairs_076
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_sym_pairs_077
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_078
    (d4_sym_pairs_079))))

end VOA.DeligneAudit.DeligneDivisor.D4
