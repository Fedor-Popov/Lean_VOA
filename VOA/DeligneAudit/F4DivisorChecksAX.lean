/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 49)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_anti_35_26 : (List.range' 26 26).all (fun d => !decide (35 < d) || antiCheck 35 d) = true := by decide +kernel

theorem f4_sym_35_26 : (List.range' 26 26).all (fun d => !decide (35 ≤ d) || symCheck 35 d) = true := by decide +kernel

theorem f4_anti_36_26 : (List.range' 26 26).all (fun d => !decide (36 < d) || antiCheck 36 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
