/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! A small closed U certificate range, [77, 85). -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem d4_small_106 : (List.range' 77 8).all UCheck = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneDivisor.D4
