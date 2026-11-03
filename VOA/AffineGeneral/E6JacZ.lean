/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 35..38 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_35_2 : jacPiece e6T 78 35 26 39 = true := by decide +kernel

theorem e6J_35_3 : jacPiece e6T 78 35 39 52 = true := by decide +kernel

theorem e6J_35_4 : jacPiece e6T 78 35 52 65 = true := by decide +kernel

theorem e6J_35_5 : jacPiece e6T 78 35 65 78 = true := by decide +kernel

theorem e6J_36_2 : jacPiece e6T 78 36 26 39 = true := by decide +kernel

theorem e6J_36_3 : jacPiece e6T 78 36 39 52 = true := by decide +kernel

theorem e6J_36_4 : jacPiece e6T 78 36 52 65 = true := by decide +kernel

theorem e6J_36_5 : jacPiece e6T 78 36 65 78 = true := by decide +kernel

theorem e6J_37_2 : jacPiece e6T 78 37 26 39 = true := by decide +kernel

theorem e6J_37_3 : jacPiece e6T 78 37 39 52 = true := by decide +kernel

theorem e6J_37_4 : jacPiece e6T 78 37 52 65 = true := by decide +kernel

theorem e6J_37_5 : jacPiece e6T 78 37 65 78 = true := by decide +kernel

theorem e6J_38_3 : jacPiece e6T 78 38 39 52 = true := by decide +kernel

theorem e6J_38_4 : jacPiece e6T 78 38 52 65 = true := by decide +kernel

theorem e6J_38_5 : jacPiece e6T 78 38 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
