/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym111

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_27 :
    (List.range' 0 27).all (fun d => !decide (27 ≤ d) || symCheck 27 d) = true := by
  decide +kernel

theorem d4_small_095 : symChecks 27 28 = true := by
  apply symChecks_row_of_range 27 28 (by decide)
  exact check_range_join 0 27 27 1 28 (by decide) (by decide) d4_sym_prefix_27
    (d4_sym_pairs_111)

end VOA.DeligneAudit.DeligneDivisor.D4
