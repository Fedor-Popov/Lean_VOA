/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSteps

/-! # `F₄` propagation steps, block A (kernel check) -/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

theorem f4StepsA_ok : f4StepsA.all stepOK = true := by decide +kernel

end VOA.DeligneAudit.DeligneSector.F4
