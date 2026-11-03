/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 7..9 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_7_0 : jacPiece f4T 52 7 0 13 = true := by decide +kernel

theorem f4J_7_1 : jacPiece f4T 52 7 13 26 = true := by decide +kernel

theorem f4J_7_2 : jacPiece f4T 52 7 26 39 = true := by decide +kernel

theorem f4J_7_3 : jacPiece f4T 52 7 39 52 = true := by decide +kernel

theorem f4J_8_0 : jacPiece f4T 52 8 0 13 = true := by decide +kernel

theorem f4J_8_1 : jacPiece f4T 52 8 13 26 = true := by decide +kernel

theorem f4J_8_2 : jacPiece f4T 52 8 26 39 = true := by decide +kernel

theorem f4J_8_3 : jacPiece f4T 52 8 39 52 = true := by decide +kernel

theorem f4J_9_0 : jacPiece f4T 52 9 0 13 = true := by decide +kernel

theorem f4J_9_1 : jacPiece f4T 52 9 13 26 = true := by decide +kernel

theorem f4J_9_2 : jacPiece f4T 52 9 26 39 = true := by decide +kernel

theorem f4J_9_3 : jacPiece f4T 52 9 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
