/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 4..6 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_4_0 : jacPiece f4T 52 4 0 13 = true := by decide +kernel

theorem f4J_4_1 : jacPiece f4T 52 4 13 26 = true := by decide +kernel

theorem f4J_4_2 : jacPiece f4T 52 4 26 39 = true := by decide +kernel

theorem f4J_4_3 : jacPiece f4T 52 4 39 52 = true := by decide +kernel

theorem f4J_5_0 : jacPiece f4T 52 5 0 13 = true := by decide +kernel

theorem f4J_5_1 : jacPiece f4T 52 5 13 26 = true := by decide +kernel

theorem f4J_5_2 : jacPiece f4T 52 5 26 39 = true := by decide +kernel

theorem f4J_5_3 : jacPiece f4T 52 5 39 52 = true := by decide +kernel

theorem f4J_6_0 : jacPiece f4T 52 6 0 13 = true := by decide +kernel

theorem f4J_6_1 : jacPiece f4T 52 6 13 26 = true := by decide +kernel

theorem f4J_6_2 : jacPiece f4T 52 6 26 39 = true := by decide +kernel

theorem f4J_6_3 : jacPiece f4T 52 6 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
