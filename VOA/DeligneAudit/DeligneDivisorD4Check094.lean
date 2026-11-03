/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym110

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_26 :
    (List.range' 0 26).all (fun d => !decide (26 ≤ d) || symCheck 26 d) = true := by
  decide +kernel

theorem d4_small_094 : symChecks 26 27 = true := by
  apply symChecks_row_of_range 26 27 (by decide)
  exact check_range_join 0 26 26 2 28 (by decide) (by decide) d4_sym_prefix_26
    (d4_sym_pairs_110)

end VOA.DeligneAudit.DeligneDivisor.D4
