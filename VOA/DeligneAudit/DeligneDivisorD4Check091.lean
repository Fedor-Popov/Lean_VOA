/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym106
import VOA.DeligneAudit.DeligneDivisorD4CheckSym107

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_23 :
    (List.range' 0 23).all (fun d => !decide (23 ≤ d) || symCheck 23 d) = true := by
  decide +kernel

theorem d4_small_091 : symChecks 23 24 = true := by
  apply symChecks_row_of_range 23 24 (by decide)
  exact check_range_join 0 23 23 5 28 (by decide) (by decide) d4_sym_prefix_23
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_106
    (d4_sym_pairs_107))

end VOA.DeligneAudit.DeligneDivisor.D4
