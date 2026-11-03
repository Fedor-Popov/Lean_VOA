/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

set_option linter.style.longLine false

/-!
# Root separation for `𝔣₄`, `32 ≤ α < 48`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4RC_sep2 : ∀ α : Fin f4Data.nr, 32 ≤ α.val → α.val < 48 → ∀ β, α ≠ β → ∃ γ, f4Data.pairT γ α ≠ f4Data.pairT γ β := by decide +kernel

end VOA.AffineGeneral.SCLie
