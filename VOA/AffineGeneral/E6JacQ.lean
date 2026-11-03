/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 16..16 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_16_1 : jacPiece e6T 78 16 13 26 = true := by decide +kernel

theorem e6J_16_2 : jacPiece e6T 78 16 26 39 = true := by decide +kernel

theorem e6J_16_3 : jacPiece e6T 78 16 39 52 = true := by decide +kernel

theorem e6J_16_4 : jacPiece e6T 78 16 52 65 = true := by decide +kernel

theorem e6J_16_5 : jacPiece e6T 78 16 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
