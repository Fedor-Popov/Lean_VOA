/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieTab

set_option linter.style.longLine false
set_option maxRecDepth 100000

/-! # `F₄` Lie data: kernel checks -/

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral.SCLie

theorem f4_cas1 : ∀ x : Fin 52, 13 ≤ x.val → x.val < 26 → casOK f4T 52 f4dl f4D 2 18 x = true := by
  decide +kernel

end VOA.DeligneAudit.F4Lie
