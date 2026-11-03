/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSingDefs

set_option maxRecDepth 100000

/-! # `F₄` singular vector: vacuum checks -/

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral

theorem f4_q2 : ∀ x : Fin 52, q2Z f4scZ f4fZ (-5) f4svTerms x = 0 := by decide +kernel

end VOA.DeligneAudit.F4Lie
