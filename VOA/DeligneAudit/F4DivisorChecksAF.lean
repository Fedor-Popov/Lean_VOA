/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 31)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_sym_16_26 : (List.range' 26 26).all (fun d => !decide (16 ≤ d) || symCheck 16 d) = true := by decide +kernel

theorem f4_anti_17_0 : (List.range' 0 26).all (fun d => !decide (17 < d) || antiCheck 17 d) = true := by decide +kernel

theorem f4_sym_17_0 : (List.range' 0 26).all (fun d => !decide (17 ≤ d) || symCheck 17 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
