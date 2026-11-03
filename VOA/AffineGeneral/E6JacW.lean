/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 27..28 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_27_2 : jacPiece e6T 78 27 26 39 = true := by decide +kernel

theorem e6J_27_3 : jacPiece e6T 78 27 39 52 = true := by decide +kernel

theorem e6J_27_4 : jacPiece e6T 78 27 52 65 = true := by decide +kernel

theorem e6J_27_5 : jacPiece e6T 78 27 65 78 = true := by decide +kernel

theorem e6J_28_2 : jacPiece e6T 78 28 26 39 = true := by decide +kernel

theorem e6J_28_3 : jacPiece e6T 78 28 39 52 = true := by decide +kernel

theorem e6J_28_4 : jacPiece e6T 78 28 52 65 = true := by decide +kernel

theorem e6J_28_5 : jacPiece e6T 78 28 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
