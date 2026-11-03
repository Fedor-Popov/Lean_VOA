/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 17..18 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_17_1 : jacPiece e6T 78 17 13 26 = true := by decide +kernel

theorem e6J_17_2 : jacPiece e6T 78 17 26 39 = true := by decide +kernel

theorem e6J_17_3 : jacPiece e6T 78 17 39 52 = true := by decide +kernel

theorem e6J_17_4 : jacPiece e6T 78 17 52 65 = true := by decide +kernel

theorem e6J_17_5 : jacPiece e6T 78 17 65 78 = true := by decide +kernel

theorem e6J_18_1 : jacPiece e6T 78 18 13 26 = true := by decide +kernel

theorem e6J_18_2 : jacPiece e6T 78 18 26 39 = true := by decide +kernel

theorem e6J_18_3 : jacPiece e6T 78 18 39 52 = true := by decide +kernel

theorem e6J_18_4 : jacPiece e6T 78 18 52 65 = true := by decide +kernel

theorem e6J_18_5 : jacPiece e6T 78 18 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
