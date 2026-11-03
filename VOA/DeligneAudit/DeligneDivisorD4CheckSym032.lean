/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Four or fewer symmetric certificate pairs in row 4. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_sym_pairs_032 :
    (List.range' 20 4).all (fun d => !decide (4 ≤ d) || symCheck 4 d) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4
