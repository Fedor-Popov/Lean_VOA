/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym091
import VOA.DeligneAudit.DeligneDivisorD4CheckSym092
import VOA.DeligneAudit.DeligneDivisorD4CheckSym093

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_17 :
    (List.range' 0 17).all (fun d => !decide (17 ≤ d) || symCheck 17 d) = true := by
  decide +kernel

theorem d4_small_085 : symChecks 17 18 = true := by
  apply symChecks_row_of_range 17 18 (by decide)
  exact check_range_join 0 17 17 11 28 (by decide) (by decide) d4_sym_prefix_17
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_sym_pairs_091
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_092
    (d4_sym_pairs_093)))

end VOA.DeligneAudit.DeligneDivisor.D4
