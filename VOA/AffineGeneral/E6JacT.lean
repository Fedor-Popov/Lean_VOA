/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 21..22 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_21_1 : jacPiece e6T 78 21 13 26 = true := by decide +kernel

theorem e6J_21_2 : jacPiece e6T 78 21 26 39 = true := by decide +kernel

theorem e6J_21_3 : jacPiece e6T 78 21 39 52 = true := by decide +kernel

theorem e6J_21_4 : jacPiece e6T 78 21 52 65 = true := by decide +kernel

theorem e6J_21_5 : jacPiece e6T 78 21 65 78 = true := by decide +kernel

theorem e6J_22_1 : jacPiece e6T 78 22 13 26 = true := by decide +kernel

theorem e6J_22_2 : jacPiece e6T 78 22 26 39 = true := by decide +kernel

theorem e6J_22_3 : jacPiece e6T 78 22 39 52 = true := by decide +kernel

theorem e6J_22_4 : jacPiece e6T 78 22 52 65 = true := by decide +kernel

theorem e6J_22_5 : jacPiece e6T 78 22 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
