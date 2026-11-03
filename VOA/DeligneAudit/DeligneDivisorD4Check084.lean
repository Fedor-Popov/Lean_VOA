/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym088
import VOA.DeligneAudit.DeligneDivisorD4CheckSym089
import VOA.DeligneAudit.DeligneDivisorD4CheckSym090

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_16 :
    (List.range' 0 16).all (fun d => !decide (16 ≤ d) || symCheck 16 d) = true := by
  decide +kernel

theorem d4_small_084 : symChecks 16 17 = true := by
  apply symChecks_row_of_range 16 17 (by decide)
  exact check_range_join 0 16 16 12 28 (by decide) (by decide) d4_sym_prefix_16
    (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_sym_pairs_088
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_089
    (d4_sym_pairs_090)))

end VOA.DeligneAudit.DeligneDivisor.D4
