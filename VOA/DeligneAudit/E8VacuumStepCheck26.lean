/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8VacuumSteps

/-!
# `E₈` propagation steps `3251..3375` (kernel checks)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

theorem stepOK_26 : ∀ s, s < 3376 → 3251 ≤ s → stepOK s = true := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
