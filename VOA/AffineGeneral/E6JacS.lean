/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 19..20 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_19_1 : jacPiece e6T 78 19 13 26 = true := by decide +kernel

theorem e6J_19_2 : jacPiece e6T 78 19 26 39 = true := by decide +kernel

theorem e6J_19_3 : jacPiece e6T 78 19 39 52 = true := by decide +kernel

theorem e6J_19_4 : jacPiece e6T 78 19 52 65 = true := by decide +kernel

theorem e6J_19_5 : jacPiece e6T 78 19 65 78 = true := by decide +kernel

theorem e6J_20_1 : jacPiece e6T 78 20 13 26 = true := by decide +kernel

theorem e6J_20_2 : jacPiece e6T 78 20 26 39 = true := by decide +kernel

theorem e6J_20_3 : jacPiece e6T 78 20 39 52 = true := by decide +kernel

theorem e6J_20_4 : jacPiece e6T 78 20 52 65 = true := by decide +kernel

theorem e6J_20_5 : jacPiece e6T 78 20 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
