/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Four or fewer symmetric certificate pairs in row 7. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_sym_pairs_049 :
    (List.range' 19 4).all (fun d => !decide (7 ≤ d) || symCheck 7 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4
