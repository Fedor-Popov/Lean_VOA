/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 5..5 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_5_0 : jacPiece e6T 78 5 0 13 = true := by decide +kernel

theorem e6J_5_1 : jacPiece e6T 78 5 13 26 = true := by decide +kernel

theorem e6J_5_2 : jacPiece e6T 78 5 26 39 = true := by decide +kernel

theorem e6J_5_3 : jacPiece e6T 78 5 39 52 = true := by decide +kernel

theorem e6J_5_4 : jacPiece e6T 78 5 52 65 = true := by decide +kernel

theorem e6J_5_5 : jacPiece e6T 78 5 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
