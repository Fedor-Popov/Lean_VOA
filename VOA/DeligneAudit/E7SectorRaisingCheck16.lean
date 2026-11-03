/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecksDefs

/-! Small exact kernel-check pilot for the unchanged E7 sector predicate. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem raising_ok_16_19 : (List.range' 16 3).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true := by
  decide +kernel

#print axioms raising_ok_16_19

end VOA.DeligneAudit.DeligneCarrier.E7
