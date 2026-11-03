/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 32..34 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_32_2 : jacPiece e6T 78 32 26 39 = true := by decide +kernel

theorem e6J_32_3 : jacPiece e6T 78 32 39 52 = true := by decide +kernel

theorem e6J_32_4 : jacPiece e6T 78 32 52 65 = true := by decide +kernel

theorem e6J_32_5 : jacPiece e6T 78 32 65 78 = true := by decide +kernel

theorem e6J_33_2 : jacPiece e6T 78 33 26 39 = true := by decide +kernel

theorem e6J_33_3 : jacPiece e6T 78 33 39 52 = true := by decide +kernel

theorem e6J_33_4 : jacPiece e6T 78 33 52 65 = true := by decide +kernel

theorem e6J_33_5 : jacPiece e6T 78 33 65 78 = true := by decide +kernel

theorem e6J_34_2 : jacPiece e6T 78 34 26 39 = true := by decide +kernel

theorem e6J_34_3 : jacPiece e6T 78 34 39 52 = true := by decide +kernel

theorem e6J_34_4 : jacPiece e6T 78 34 52 65 = true := by decide +kernel

theorem e6J_34_5 : jacPiece e6T 78 34 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
