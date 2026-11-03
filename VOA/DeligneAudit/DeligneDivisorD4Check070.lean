/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym014
import VOA.DeligneAudit.DeligneDivisorD4CheckSym015
import VOA.DeligneAudit.DeligneDivisorD4CheckSym016
import VOA.DeligneAudit.DeligneDivisorD4CheckSym017
import VOA.DeligneAudit.DeligneDivisorD4CheckSym018
import VOA.DeligneAudit.DeligneDivisorD4CheckSym019
import VOA.DeligneAudit.DeligneDivisorD4CheckSym020

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_2 :
    (List.range' 0 2).all (fun d => !decide (2 ≤ d) || symCheck 2 d) = true := by
  decide +kernel

theorem d4_small_070 : symChecks 2 3 = true := by
  apply symChecks_row_of_range 2 3 (by decide)
  exact check_range_join 0 2 2 26 28 (by decide) (by decide) d4_sym_prefix_2
    (check_range_join 2 4 6 22 26 (by decide) (by decide) d4_sym_pairs_014
    (check_range_join 6 4 10 18 22 (by decide) (by decide) d4_sym_pairs_015
    (check_range_join 10 4 14 14 18 (by decide) (by decide) d4_sym_pairs_016
    (check_range_join 14 4 18 10 14 (by decide) (by decide) d4_sym_pairs_017
    (check_range_join 18 4 22 6 10 (by decide) (by decide) d4_sym_pairs_018
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_019
    (d4_sym_pairs_020)))))))

end VOA.DeligneAudit.DeligneDivisor.D4
