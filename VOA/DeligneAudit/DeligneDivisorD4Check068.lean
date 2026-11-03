/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckSym000
import VOA.DeligneAudit.DeligneDivisorD4CheckSym001
import VOA.DeligneAudit.DeligneDivisorD4CheckSym002
import VOA.DeligneAudit.DeligneDivisorD4CheckSym003
import VOA.DeligneAudit.DeligneDivisorD4CheckSym004
import VOA.DeligneAudit.DeligneDivisorD4CheckSym005
import VOA.DeligneAudit.DeligneDivisorD4CheckSym006

/-! Assemble one row from small independent pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem d4_sym_prefix_0 :
    (List.range' 0 0).all (fun d => !decide (0 ≤ d) || symCheck 0 d) = true := by
  decide +kernel

theorem d4_small_068 : symChecks 0 1 = true := by
  apply symChecks_row_of_range 0 1 (by decide)
  exact check_range_join 0 0 0 28 28 (by decide) (by decide) d4_sym_prefix_0
    (check_range_join 0 4 4 24 28 (by decide) (by decide) d4_sym_pairs_000
    (check_range_join 4 4 8 20 24 (by decide) (by decide) d4_sym_pairs_001
    (check_range_join 8 4 12 16 20 (by decide) (by decide) d4_sym_pairs_002
    (check_range_join 12 4 16 12 16 (by decide) (by decide) d4_sym_pairs_003
    (check_range_join 16 4 20 8 12 (by decide) (by decide) d4_sym_pairs_004
    (check_range_join 20 4 24 4 8 (by decide) (by decide) d4_sym_pairs_005
    (d4_sym_pairs_006)))))))

end VOA.DeligneAudit.DeligneDivisor.D4
