/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym057
import VOA.DeligneAudit.DeligneDivisorD4CheckSym058
import VOA.DeligneAudit.DeligneDivisorD4CheckSym059
import VOA.DeligneAudit.DeligneDivisorD4CheckSym060
import VOA.DeligneAudit.DeligneDivisorD4CheckSym061

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_9 :
    (List.range' 0 9).all (fun d => !decide (9 ≤ d) || symCheck 9 d) = true := by
  decide +kernel

theorem d4_small_077 : symChecks 9 10 = true := by
  apply symChecks_row_of_range 9 10 (by decide)
  exact check_range_join 0 9 9 19 28 (by decide) (by decide) d4_sym_prefix_9
    (check_range_join 9 4 13 15 19 (by decide) (by decide) d4_sym_pairs_057
    (check_range_join 13 4 17 11 15 (by decide) (by decide) d4_sym_pairs_058
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_sym_pairs_059
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_sym_pairs_060
    (d4_sym_pairs_061)))))

end VOA.DeligneAudit.DeligneDivisor.D4
