/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 53)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_anti_41_26 : (List.range' 26 26).all (fun d => !decide (41 < d) || antiCheck 41 d) = true := by decide +kernel

theorem f4_sym_41_26 : (List.range' 26 26).all (fun d => !decide (41 ≤ d) || symCheck 41 d) = true := by decide +kernel

theorem f4_anti_42_26 : (List.range' 26 26).all (fun d => !decide (42 < d) || antiCheck 42 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
