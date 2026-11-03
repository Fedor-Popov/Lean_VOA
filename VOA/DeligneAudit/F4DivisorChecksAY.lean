/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 50)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_sym_36_26 : (List.range' 26 26).all (fun d => !decide (36 ≤ d) || symCheck 36 d) = true := by decide +kernel

theorem f4_anti_37_26 : (List.range' 26 26).all (fun d => !decide (37 < d) || antiCheck 37 d) = true := by decide +kernel

theorem f4_sym_37_26 : (List.range' 26 26).all (fun d => !decide (37 ≤ d) || symCheck 37 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
