/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym028
import VOA.DeligneAudit.DeligneDivisorD4CheckSym029
import VOA.DeligneAudit.DeligneDivisorD4CheckSym030
import VOA.DeligneAudit.DeligneDivisorD4CheckSym031
import VOA.DeligneAudit.DeligneDivisorD4CheckSym032
import VOA.DeligneAudit.DeligneDivisorD4CheckSym033

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_4 :
    (List.range' 0 4).all (fun d => !decide (4 ≤ d) || symCheck 4 d) = true := by
  decide +kernel

theorem d4_small_072 : symChecks 4 5 = true := by
  apply symChecks_row_of_range 4 5 (by decide)
  exact check_range_join 0 4 4 24 28 (by decide) (by decide) d4_sym_prefix_4
    (check_range_join 4 4 8 20 24 (by decide) (by decide) d4_sym_pairs_028
    (check_range_join 8 4 12 16 20 (by decide) (by decide) d4_sym_pairs_029
    (check_range_join 12 4 16 12 16 (by decide) (by decide) d4_sym_pairs_030
    (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_sym_pairs_031
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_032
    (d4_sym_pairs_033))))))

end VOA.DeligneAudit.DeligneDivisor.D4
