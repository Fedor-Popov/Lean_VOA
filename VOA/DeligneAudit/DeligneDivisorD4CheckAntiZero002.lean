/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Four or fewer antisymmetric input pairs in row zero. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_anti_zero_002 :
    (List.range' 9 4).all (fun d => !decide (0 < d) || antiCheck 0 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4
