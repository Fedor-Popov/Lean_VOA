/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2Table

set_option linter.style.longLine false

/-!
# Antisymmetry of `𝔤₂`, rows `7 ≤ i < 10`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem g2_anti2 : antiChunk g2T 14 7 10 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
