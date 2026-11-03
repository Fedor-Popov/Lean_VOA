/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Coroots commute in `𝔢₆`, `0 ≤ α < 24`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6RC_hhb0 : ∀ α : Fin e6Data.nr, 0 ≤ α.val → α.val < 24 → ∀ β, zeroL (brL e6T (hL e6T e6Data α) (hL e6T e6Data β)) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
