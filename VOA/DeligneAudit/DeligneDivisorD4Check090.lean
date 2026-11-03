/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym104
import VOA.DeligneAudit.DeligneDivisorD4CheckSym105

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_22 :
    (List.range' 0 22).all (fun d => !decide (22 ≤ d) || symCheck 22 d) = true := by
  decide +kernel

theorem d4_small_090 : symChecks 22 23 = true := by
  apply symChecks_row_of_range 22 23 (by decide)
  exact check_range_join 0 22 22 6 28 (by decide) (by decide) d4_sym_prefix_22
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_104
    (d4_sym_pairs_105))

end VOA.DeligneAudit.DeligneDivisor.D4
