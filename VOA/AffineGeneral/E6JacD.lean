/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 3..3 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_3_0 : jacPiece e6T 78 3 0 13 = true := by decide +kernel

theorem e6J_3_1 : jacPiece e6T 78 3 13 26 = true := by decide +kernel

theorem e6J_3_2 : jacPiece e6T 78 3 26 39 = true := by decide +kernel

theorem e6J_3_3 : jacPiece e6T 78 3 39 52 = true := by decide +kernel

theorem e6J_3_4 : jacPiece e6T 78 3 52 65 = true := by decide +kernel

theorem e6J_3_5 : jacPiece e6T 78 3 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
