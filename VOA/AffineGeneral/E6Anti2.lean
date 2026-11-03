/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Antisymmetry of `𝔢₆`, rows `39 ≤ i < 58`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6_anti2 : antiChunk e6T 78 39 58 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
