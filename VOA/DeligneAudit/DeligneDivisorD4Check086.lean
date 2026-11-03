/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym094
import VOA.DeligneAudit.DeligneDivisorD4CheckSym095
import VOA.DeligneAudit.DeligneDivisorD4CheckSym096

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_18 :
    (List.range' 0 18).all (fun d => !decide (18 ≤ d) || symCheck 18 d) = true := by
  decide +kernel

theorem d4_small_086 : symChecks 18 19 = true := by
  apply symChecks_row_of_range 18 19 (by decide)
  exact check_range_join 0 18 18 10 28 (by decide) (by decide) d4_sym_prefix_18
    (check_range_join 18 4 22 6 10 (by decide) (by decide) d4_sym_pairs_094
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_095
    (d4_sym_pairs_096)))

end VOA.DeligneAudit.DeligneDivisor.D4
