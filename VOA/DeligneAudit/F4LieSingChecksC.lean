/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSingDefs

set_option maxRecDepth 100000

/-! # `F₄` singular vector: weight-one checks, `14 ≤ x < 21` -/

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral

theorem f4_q1_2 : ∀ x g : Fin 52, 14 ≤ x.val → x.val < 21 →
    q1Z f4scZ f4fZ (-5) 2 f4svTerms x g = 0 := by
  decide +kernel

end VOA.DeligneAudit.F4Lie
