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

theorem wtLink : wtLinkOK = true := by decide +kernel

#print axioms wtLink

end VOA.DeligneAudit.DeligneCarrier.E7
