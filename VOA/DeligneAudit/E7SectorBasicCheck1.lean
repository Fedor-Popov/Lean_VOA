/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecksDefs

/-! An unchanged basic E7 sector kernel check with light imports. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

theorem e7_wt_pos : ∀ y k, 0 ≤ E7Lie.wt y k + thetaV k := by decide +kernel

#print axioms e7_wt_pos

end VOA.DeligneAudit.DeligneCarrier.E7
