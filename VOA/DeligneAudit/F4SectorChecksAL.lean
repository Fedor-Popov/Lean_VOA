/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorTables

/-!
# F4 sector data: kernel checks (blocks 37)
-/

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem cycRoot_ok : vecs 0 = [(45, 1)] ∧ (cpar 0).2.2 = 0 := by decide +kernel

theorem vecLen : vecR.length = 185 := by decide +kernel

theorem cartan_ok : ∀ y : Fin 52,
    fZ br 0 y 45 = (if y.val = 45 then -2 else 0) ∧
    fZ br 1 y 45 = (if y.val = 45 then -1 else 0) ∧
    fZ br 2 y 45 = (if y.val = 45 then 0 else 0) ∧
    fZ br 3 y 45 = (if y.val = 45 then 1 else 0) := by decide +kernel

end VOA.DeligneAudit.DeligneSector.F4
