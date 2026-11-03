/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 3..3 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_3_0 : jacPiece f4T 52 3 0 13 = true := by decide +kernel

theorem f4J_3_1 : jacPiece f4T 52 3 13 26 = true := by decide +kernel

theorem f4J_3_2 : jacPiece f4T 52 3 26 39 = true := by decide +kernel

theorem f4J_3_3 : jacPiece f4T 52 3 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
