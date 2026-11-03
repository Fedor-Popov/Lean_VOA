/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 25..26 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_25_2 : jacPiece e6T 78 25 26 39 = true := by decide +kernel

theorem e6J_25_3 : jacPiece e6T 78 25 39 52 = true := by decide +kernel

theorem e6J_25_4 : jacPiece e6T 78 25 52 65 = true := by decide +kernel

theorem e6J_25_5 : jacPiece e6T 78 25 65 78 = true := by decide +kernel

theorem e6J_26_2 : jacPiece e6T 78 26 26 39 = true := by decide +kernel

theorem e6J_26_3 : jacPiece e6T 78 26 39 52 = true := by decide +kernel

theorem e6J_26_4 : jacPiece e6T 78 26 52 65 = true := by decide +kernel

theorem e6J_26_5 : jacPiece e6T 78 26 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
