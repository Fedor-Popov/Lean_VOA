/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym108

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_24 :
    (List.range' 0 24).all (fun d => !decide (24 ≤ d) || symCheck 24 d) = true := by
  decide +kernel

theorem d4_small_092 : symChecks 24 25 = true := by
  apply symChecks_row_of_range 24 25 (by decide)
  exact check_range_join 0 24 24 4 28 (by decide) (by decide) d4_sym_prefix_24
    (d4_sym_pairs_108)

end VOA.DeligneAudit.DeligneDivisor.D4
