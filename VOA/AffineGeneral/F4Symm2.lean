/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

set_option linter.style.longLine false

/-!
# Symmetry of the root graph of `𝔣₄`, `32 ≤ α < 48`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4RC_symm2 : ∀ α : Fin f4Data.nr, 32 ≤ α.val → α.val < 48 → ∀ β, f4Data.pairT α β ≠ 0 → f4Data.pairT β α ≠ 0 := by decide +kernel

end VOA.AffineGeneral.SCLie
