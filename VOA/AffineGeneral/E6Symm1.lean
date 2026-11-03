/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Symmetry of the root graph of `𝔢₆`, `24 ≤ α < 48`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6RC_symm1 : ∀ α : Fin e6Data.nr, 24 ≤ α.val → α.val < 48 → ∀ β, e6Data.pairT α β ≠ 0 → e6Data.pairT β α ≠ 0 := by decide +kernel

end VOA.AffineGeneral.SCLie
