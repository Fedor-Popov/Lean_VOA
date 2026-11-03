/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2Table

set_option linter.style.longLine false

/-!
# Symmetry of the root graph of `𝔤₂`, `4 ≤ α < 8`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem g2RC_symm1 : ∀ α : Fin g2Data.nr, 4 ≤ α.val → α.val < 8 → ∀ β, g2Data.pairT α β ≠ 0 → g2Data.pairT β α ≠ 0 := by decide +kernel

end VOA.AffineGeneral.SCLie
