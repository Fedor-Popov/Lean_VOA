/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 10..13 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_10_0 : jacPiece f4T 52 10 0 13 = true := by decide +kernel

theorem f4J_10_1 : jacPiece f4T 52 10 13 26 = true := by decide +kernel

theorem f4J_10_2 : jacPiece f4T 52 10 26 39 = true := by decide +kernel

theorem f4J_10_3 : jacPiece f4T 52 10 39 52 = true := by decide +kernel

theorem f4J_11_0 : jacPiece f4T 52 11 0 13 = true := by decide +kernel

theorem f4J_11_1 : jacPiece f4T 52 11 13 26 = true := by decide +kernel

theorem f4J_11_2 : jacPiece f4T 52 11 26 39 = true := by decide +kernel

theorem f4J_11_3 : jacPiece f4T 52 11 39 52 = true := by decide +kernel

theorem f4J_12_1 : jacPiece f4T 52 12 13 26 = true := by decide +kernel

theorem f4J_12_2 : jacPiece f4T 52 12 26 39 = true := by decide +kernel

theorem f4J_12_3 : jacPiece f4T 52 12 39 52 = true := by decide +kernel

theorem f4J_13_1 : jacPiece f4T 52 13 13 26 = true := by decide +kernel

theorem f4J_13_2 : jacPiece f4T 52 13 26 39 = true := by decide +kernel

theorem f4J_13_3 : jacPiece f4T 52 13 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
