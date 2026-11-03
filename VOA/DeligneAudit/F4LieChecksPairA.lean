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

theorem f4_pair0 : pairChunk 52 f4Gm f4dl f4D 0 26 = true := by decide +kernel

end VOA.DeligneAudit.F4Lie
