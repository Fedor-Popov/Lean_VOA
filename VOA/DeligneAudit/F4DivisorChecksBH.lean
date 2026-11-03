/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 59)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_anti_50_26 : (List.range' 26 26).all (fun d => !decide (50 < d) || antiCheck 50 d) = true := by decide +kernel

theorem f4_sym_50_26 : (List.range' 26 26).all (fun d => !decide (50 ≤ d) || symCheck 50 d) = true := by decide +kernel

theorem f4_sym_51_26 : (List.range' 26 26).all (fun d => !decide (51 ≤ d) || symCheck 51 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
