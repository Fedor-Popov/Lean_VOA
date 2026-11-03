/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2Table

set_option linter.style.longLine false

/-!
# Coroots commute in `𝔤₂`, `0 ≤ α < 4`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem g2RC_hhb0 : ∀ α : Fin g2Data.nr, 0 ≤ α.val → α.val < 4 → ∀ β, zeroL (brL g2T (hL g2T g2Data α) (hL g2T g2Data β)) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
