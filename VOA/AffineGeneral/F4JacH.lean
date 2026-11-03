/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

/-!
# Cyclic Jacobi for `𝔣₄`, rows 14..19 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4J_14_1 : jacPiece f4T 52 14 13 26 = true := by decide +kernel

theorem f4J_14_2 : jacPiece f4T 52 14 26 39 = true := by decide +kernel

theorem f4J_14_3 : jacPiece f4T 52 14 39 52 = true := by decide +kernel

theorem f4J_15_1 : jacPiece f4T 52 15 13 26 = true := by decide +kernel

theorem f4J_15_2 : jacPiece f4T 52 15 26 39 = true := by decide +kernel

theorem f4J_15_3 : jacPiece f4T 52 15 39 52 = true := by decide +kernel

theorem f4J_16_1 : jacPiece f4T 52 16 13 26 = true := by decide +kernel

theorem f4J_16_2 : jacPiece f4T 52 16 26 39 = true := by decide +kernel

theorem f4J_16_3 : jacPiece f4T 52 16 39 52 = true := by decide +kernel

theorem f4J_17_1 : jacPiece f4T 52 17 13 26 = true := by decide +kernel

theorem f4J_17_2 : jacPiece f4T 52 17 26 39 = true := by decide +kernel

theorem f4J_17_3 : jacPiece f4T 52 17 39 52 = true := by decide +kernel

theorem f4J_18_1 : jacPiece f4T 52 18 13 26 = true := by decide +kernel

theorem f4J_18_2 : jacPiece f4T 52 18 26 39 = true := by decide +kernel

theorem f4J_18_3 : jacPiece f4T 52 18 39 52 = true := by decide +kernel

theorem f4J_19_1 : jacPiece f4T 52 19 13 26 = true := by decide +kernel

theorem f4J_19_2 : jacPiece f4T 52 19 26 39 = true := by decide +kernel

theorem f4J_19_3 : jacPiece f4T 52 19 39 52 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
