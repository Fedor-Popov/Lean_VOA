/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym080
import VOA.DeligneAudit.DeligneDivisorD4CheckSym081
import VOA.DeligneAudit.DeligneDivisorD4CheckSym082
import VOA.DeligneAudit.DeligneDivisorD4CheckSym083

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_14 :
    (List.range' 0 14).all (fun d => !decide (14 ≤ d) || symCheck 14 d) = true := by
  decide +kernel

theorem d4_small_082 : symChecks 14 15 = true := by
  apply symChecks_row_of_range 14 15 (by decide)
  exact check_range_join 0 14 14 14 28 (by decide) (by decide) d4_sym_prefix_14
    (check_range_join 14 4 18 10 14 (by decide) (by decide) d4_sym_pairs_080
    (check_range_join 18 4 22 6 10 (by decide) (by decide) d4_sym_pairs_081
    (check_range_join 22 4 26 2 6 (by decide) (by decide) d4_sym_pairs_082
    (d4_sym_pairs_083))))

end VOA.DeligneAudit.DeligneDivisor.D4
