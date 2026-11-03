/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym102
import VOA.DeligneAudit.DeligneDivisorD4CheckSym103

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_21 :
    (List.range' 0 21).all (fun d => !decide (21 ≤ d) || symCheck 21 d) = true := by
  decide +kernel

theorem d4_small_089 : symChecks 21 22 = true := by
  apply symChecks_row_of_range 21 22 (by decide)
  exact check_range_join 0 21 21 7 28 (by decide) (by decide) d4_sym_prefix_21
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_102
    (d4_sym_pairs_103))

end VOA.DeligneAudit.DeligneDivisor.D4
