/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4CheckAssembly
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero000
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero001
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero002
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero003
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero004
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero005
import VOA.DeligneAudit.DeligneDivisorD4CheckAntiZero006

/-! Assemble the first antisymmetric row from small pair checks. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

private theorem anti_zero_prefix :
    (List.range' 0 1).all (fun d => !decide (0 < d) || antiCheck 0 d) = true := by
  decide +kernel

theorem d4_small_040 : antiChecks 0 1 = true := by
  apply antiChecks_row_of_range 0 1 (by decide)
  exact check_range_join 0 1 1 27 28 (by decide) (by decide) anti_zero_prefix
    (check_range_join 1 4 5 23 27 (by decide) (by decide) d4_anti_zero_000
    (check_range_join 5 4 9 19 23 (by decide) (by decide) d4_anti_zero_001
    (check_range_join 9 4 13 15 19 (by decide) (by decide) d4_anti_zero_002
    (check_range_join 13 4 17 11 15 (by decide) (by decide) d4_anti_zero_003
    (check_range_join 17 4 21 7 11 (by decide) (by decide) d4_anti_zero_004
    (check_range_join 21 4 25 3 7 (by decide) (by decide) d4_anti_zero_005
    (d4_anti_zero_006)))))))

end VOA.DeligneAudit.DeligneDivisor.D4
