/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 20..29 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_20_1 : jacPiece f4T 52 20 13 26 = true := by decide +kernel

theorem f4J_20_2 : jacPiece f4T 52 20 26 39 = true := by decide +kernel

theorem f4J_20_3 : jacPiece f4T 52 20 39 52 = true := by decide +kernel

theorem f4J_21_1 : jacPiece f4T 52 21 13 26 = true := by decide +kernel

theorem f4J_21_2 : jacPiece f4T 52 21 26 39 = true := by decide +kernel

theorem f4J_21_3 : jacPiece f4T 52 21 39 52 = true := by decide +kernel

theorem f4J_22_1 : jacPiece f4T 52 22 13 26 = true := by decide +kernel

theorem f4J_22_2 : jacPiece f4T 52 22 26 39 = true := by decide +kernel

theorem f4J_22_3 : jacPiece f4T 52 22 39 52 = true := by decide +kernel

theorem f4J_23_1 : jacPiece f4T 52 23 13 26 = true := by decide +kernel

theorem f4J_23_2 : jacPiece f4T 52 23 26 39 = true := by decide +kernel

theorem f4J_23_3 : jacPiece f4T 52 23 39 52 = true := by decide +kernel

theorem f4J_24_1 : jacPiece f4T 52 24 13 26 = true := by decide +kernel

theorem f4J_24_2 : jacPiece f4T 52 24 26 39 = true := by decide +kernel

theorem f4J_24_3 : jacPiece f4T 52 24 39 52 = true := by decide +kernel

theorem f4J_25_2 : jacPiece f4T 52 25 26 39 = true := by decide +kernel

theorem f4J_25_3 : jacPiece f4T 52 25 39 52 = true := by decide +kernel

theorem f4J_26_2 : jacPiece f4T 52 26 26 39 = true := by decide +kernel

theorem f4J_26_3 : jacPiece f4T 52 26 39 52 = true := by decide +kernel

theorem f4J_27_2 : jacPiece f4T 52 27 26 39 = true := by decide +kernel

theorem f4J_27_3 : jacPiece f4T 52 27 39 52 = true := by decide +kernel

theorem f4J_28_2 : jacPiece f4T 52 28 26 39 = true := by decide +kernel

theorem f4J_28_3 : jacPiece f4T 52 28 39 52 = true := by decide +kernel

theorem f4J_29_2 : jacPiece f4T 52 29 26 39 = true := by decide +kernel

theorem f4J_29_3 : jacPiece f4T 52 29 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
