/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym109

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_25 :
    (List.range' 0 25).all (fun d => !decide (25 ≤ d) || symCheck 25 d) = true := by
  decide +kernel

theorem d4_small_093 : symChecks 25 26 = true := by
  apply symChecks_row_of_range 25 26 (by decide)
  exact check_range_join 0 25 25 3 28 (by decide) (by decide) d4_sym_prefix_25
    (d4_sym_pairs_109)

end VOA.DeligneAudit.DeligneDivisor.D4
