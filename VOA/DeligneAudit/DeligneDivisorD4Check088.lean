/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym100
import VOA.DeligneAudit.DeligneDivisorD4CheckSym101

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_20 :
    (List.range' 0 20).all (fun d => !decide (20 ≤ d) || symCheck 20 d) = true := by
  decide +kernel

theorem d4_small_088 : symChecks 20 21 = true := by
  apply symChecks_row_of_range 20 21 (by decide)
  exact check_range_join 0 20 20 8 28 (by decide) (by decide) d4_sym_prefix_20
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_100
    (d4_sym_pairs_101))

end VOA.DeligneAudit.DeligneDivisor.D4
