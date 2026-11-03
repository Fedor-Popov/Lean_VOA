/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym072
import VOA.DeligneAudit.DeligneDivisorD4CheckSym073
import VOA.DeligneAudit.DeligneDivisorD4CheckSym074
import VOA.DeligneAudit.DeligneDivisorD4CheckSym075

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_12 :
    (List.range' 0 12).all (fun d => !decide (12 ≤ d) || symCheck 12 d) = true := by
  decide +kernel

theorem d4_small_080 : symChecks 12 13 = true := by
  apply symChecks_row_of_range 12 13 (by decide)
  exact check_range_join 0 12 12 16 28 (by decide) (by decide) d4_sym_prefix_12
    (check_range_join 12 4 16 12 16 (by decide) (by decide) d4_sym_pairs_072
    (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_sym_pairs_073
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_074
    (d4_sym_pairs_075))))

end VOA.DeligneAudit.DeligneDivisor.D4
