/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

set_option linter.style.longLine false

/-!
# Index bounds of `𝔣₄`, rows `0 ≤ i < 13`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4_bound0 : boundChunk f4T 52 0 13 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
