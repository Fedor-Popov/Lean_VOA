/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Index bounds of `𝔢₆`, rows `19 ≤ i < 39`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_bound1 : boundChunk e6T 78 19 39 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
