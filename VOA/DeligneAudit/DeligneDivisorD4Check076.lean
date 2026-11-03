/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym052
import VOA.DeligneAudit.DeligneDivisorD4CheckSym053
import VOA.DeligneAudit.DeligneDivisorD4CheckSym054
import VOA.DeligneAudit.DeligneDivisorD4CheckSym055
import VOA.DeligneAudit.DeligneDivisorD4CheckSym056

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_8 :
    (List.range' 0 8).all (fun d => !decide (8 ≤ d) || symCheck 8 d) = true := by
  decide +kernel

theorem d4_small_076 : symChecks 8 9 = true := by
  apply symChecks_row_of_range 8 9 (by decide)
  exact check_range_join 0 8 8 20 28 (by decide) (by decide) d4_sym_prefix_8
    (check_range_join 8 4 12 16 20 (by decide) (by decide) d4_sym_pairs_052
    (check_range_join 12 4 16 12 16 (by decide) (by decide) d4_sym_pairs_053
    (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_sym_pairs_054
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_055
    (d4_sym_pairs_056)))))

end VOA.DeligneAudit.DeligneDivisor.D4
