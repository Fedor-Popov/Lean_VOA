/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym097
import VOA.DeligneAudit.DeligneDivisorD4CheckSym098
import VOA.DeligneAudit.DeligneDivisorD4CheckSym099

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_19 :
    (List.range' 0 19).all (fun d => !decide (19 ≤ d) || symCheck 19 d) = true := by
  decide +kernel

theorem d4_small_087 : symChecks 19 20 = true := by
  apply symChecks_row_of_range 19 20 (by decide)
  exact check_range_join 0 19 19 9 28 (by decide) (by decide) d4_sym_prefix_19
    (check_range_join 19 4 23 5 9 (by decide) (by decide) d4_sym_pairs_097
    (check_range_join 23 4 27 1 5 (by decide) (by decide) d4_sym_pairs_098
    (d4_sym_pairs_099)))

end VOA.DeligneAudit.DeligneDivisor.D4
