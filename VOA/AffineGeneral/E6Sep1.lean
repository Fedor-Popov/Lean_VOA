/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Root separation for `𝔢₆`, `24 ≤ α < 48`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6RC_sep1 : ∀ α : Fin e6Data.nr, 24 ≤ α.val → α.val < 48 → ∀ β, α ≠ β → ∃ γ, e6Data.pairT γ α ≠ e6Data.pairT γ β := by decide +kernel

end VOA.AffineGeneral.SCLie
