/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorData

/-!
# F4 pair-comparison certificates: kernel checks (blocks 52)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_sym_39_26 : (List.range' 26 26).all (fun d => !decide (39 ≤ d) || symCheck 39 d) = true := by decide +kernel

theorem f4_anti_40_26 : (List.range' 26 26).all (fun d => !decide (40 < d) || antiCheck 40 d) = true := by decide +kernel

theorem f4_sym_40_26 : (List.range' 26 26).all (fun d => !decide (40 ≤ d) || symCheck 40 d) = true := by decide +kernel

end VOA.DeligneAudit.DeligneDivisor.F4
