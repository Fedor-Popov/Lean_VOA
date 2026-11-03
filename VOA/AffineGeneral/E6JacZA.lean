/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 39..43 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_39_3 : jacPiece e6T 78 39 39 52 = true := by decide +kernel

theorem e6J_39_4 : jacPiece e6T 78 39 52 65 = true := by decide +kernel

theorem e6J_39_5 : jacPiece e6T 78 39 65 78 = true := by decide +kernel

theorem e6J_40_3 : jacPiece e6T 78 40 39 52 = true := by decide +kernel

theorem e6J_40_4 : jacPiece e6T 78 40 52 65 = true := by decide +kernel

theorem e6J_40_5 : jacPiece e6T 78 40 65 78 = true := by decide +kernel

theorem e6J_41_3 : jacPiece e6T 78 41 39 52 = true := by decide +kernel

theorem e6J_41_4 : jacPiece e6T 78 41 52 65 = true := by decide +kernel

theorem e6J_41_5 : jacPiece e6T 78 41 65 78 = true := by decide +kernel

theorem e6J_42_3 : jacPiece e6T 78 42 39 52 = true := by decide +kernel

theorem e6J_42_4 : jacPiece e6T 78 42 52 65 = true := by decide +kernel

theorem e6J_42_5 : jacPiece e6T 78 42 65 78 = true := by decide +kernel

theorem e6J_43_3 : jacPiece e6T 78 43 39 52 = true := by decide +kernel

theorem e6J_43_4 : jacPiece e6T 78 43 52 65 = true := by decide +kernel

theorem e6J_43_5 : jacPiece e6T 78 43 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
