/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Four or fewer symmetric certificate pairs in row 22. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_sym_pairs_104 :
    (List.range' 22 4).all (fun d => !decide (22 ≤ d) || symCheck 22 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4
