/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

set_option linter.style.longLine false

/-!
# Coroot action on root vectors of `𝔣₄`, `0 ≤ α < 16`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4RC_hbe0 : ∀ α : Fin f4Data.nr, 0 ≤ α.val → α.val < 16 → ∀ β, zeroL (brL f4T (hL f4T f4Data α) (eL f4Data β) ++ scale (-(f4Data.pairT α β)) (eL f4Data β)) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
