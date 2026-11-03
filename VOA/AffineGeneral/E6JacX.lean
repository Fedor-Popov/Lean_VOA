/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 29..31 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_29_2 : jacPiece e6T 78 29 26 39 = true := by decide +kernel

theorem e6J_29_3 : jacPiece e6T 78 29 39 52 = true := by decide +kernel

theorem e6J_29_4 : jacPiece e6T 78 29 52 65 = true := by decide +kernel

theorem e6J_29_5 : jacPiece e6T 78 29 65 78 = true := by decide +kernel

theorem e6J_30_2 : jacPiece e6T 78 30 26 39 = true := by decide +kernel

theorem e6J_30_3 : jacPiece e6T 78 30 39 52 = true := by decide +kernel

theorem e6J_30_4 : jacPiece e6T 78 30 52 65 = true := by decide +kernel

theorem e6J_30_5 : jacPiece e6T 78 30 65 78 = true := by decide +kernel

theorem e6J_31_2 : jacPiece e6T 78 31 26 39 = true := by decide +kernel

theorem e6J_31_3 : jacPiece e6T 78 31 39 52 = true := by decide +kernel

theorem e6J_31_4 : jacPiece e6T 78 31 52 65 = true := by decide +kernel

theorem e6J_31_5 : jacPiece e6T 78 31 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
