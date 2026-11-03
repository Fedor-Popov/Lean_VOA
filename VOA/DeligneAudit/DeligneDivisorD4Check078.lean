/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym062
import VOA.DeligneAudit.DeligneDivisorD4CheckSym063
import VOA.DeligneAudit.DeligneDivisorD4CheckSym064
import VOA.DeligneAudit.DeligneDivisorD4CheckSym065
import VOA.DeligneAudit.DeligneDivisorD4CheckSym066

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_10 :
    (List.range' 0 10).all (fun d => !decide (10 ≤ d) || symCheck 10 d) = true := by
  decide +kernel

theorem d4_small_078 : symChecks 10 11 = true := by
  apply symChecks_row_of_range 10 11 (by decide)
  exact check_range_join 0 10 10 18 28 (by decide) (by decide) d4_sym_prefix_10
    (check_range_join 10 4 14 14 18 (by decide) (by decide) d4_sym_pairs_062
    (check_range_join 14 4 18 10 14 (by decide) (by decide) d4_sym_pairs_063
    (check_range_join 18 4 22 6 10 (by decide) (by decide) d4_sym_pairs_064
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_065
    (d4_sym_pairs_066)))))

end VOA.DeligneAudit.DeligneDivisor.D4
