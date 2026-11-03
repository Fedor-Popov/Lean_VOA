/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 2..2 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_2_0 : jacPiece e6T 78 2 0 13 = true := by decide +kernel

theorem e6J_2_1 : jacPiece e6T 78 2 13 26 = true := by decide +kernel

theorem e6J_2_2 : jacPiece e6T 78 2 26 39 = true := by decide +kernel

theorem e6J_2_3 : jacPiece e6T 78 2 39 52 = true := by decide +kernel

theorem e6J_2_4 : jacPiece e6T 78 2 52 65 = true := by decide +kernel

theorem e6J_2_5 : jacPiece e6T 78 2 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
