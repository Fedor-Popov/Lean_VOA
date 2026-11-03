/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 1..1 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_1_0 : jacPiece f4T 52 1 0 13 = true := by decide +kernel

theorem f4J_1_1 : jacPiece f4T 52 1 13 26 = true := by decide +kernel

theorem f4J_1_2 : jacPiece f4T 52 1 26 39 = true := by decide +kernel

theorem f4J_1_3 : jacPiece f4T 52 1 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
