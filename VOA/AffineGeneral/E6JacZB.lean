/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

/-!
# Cyclic Jacobi for `𝔢₆`, rows 44..51 (one declaration per row and column block)
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6J_44_3 : jacPiece e6T 78 44 39 52 = true := by decide +kernel

theorem e6J_44_4 : jacPiece e6T 78 44 52 65 = true := by decide +kernel

theorem e6J_44_5 : jacPiece e6T 78 44 65 78 = true := by decide +kernel

theorem e6J_45_3 : jacPiece e6T 78 45 39 52 = true := by decide +kernel

theorem e6J_45_4 : jacPiece e6T 78 45 52 65 = true := by decide +kernel

theorem e6J_45_5 : jacPiece e6T 78 45 65 78 = true := by decide +kernel

theorem e6J_46_3 : jacPiece e6T 78 46 39 52 = true := by decide +kernel

theorem e6J_46_4 : jacPiece e6T 78 46 52 65 = true := by decide +kernel

theorem e6J_46_5 : jacPiece e6T 78 46 65 78 = true := by decide +kernel

theorem e6J_47_3 : jacPiece e6T 78 47 39 52 = true := by decide +kernel

theorem e6J_47_4 : jacPiece e6T 78 47 52 65 = true := by decide +kernel

theorem e6J_47_5 : jacPiece e6T 78 47 65 78 = true := by decide +kernel

theorem e6J_48_3 : jacPiece e6T 78 48 39 52 = true := by decide +kernel

theorem e6J_48_4 : jacPiece e6T 78 48 52 65 = true := by decide +kernel

theorem e6J_48_5 : jacPiece e6T 78 48 65 78 = true := by decide +kernel

theorem e6J_49_3 : jacPiece e6T 78 49 39 52 = true := by decide +kernel

theorem e6J_49_4 : jacPiece e6T 78 49 52 65 = true := by decide +kernel

theorem e6J_49_5 : jacPiece e6T 78 49 65 78 = true := by decide +kernel

theorem e6J_50_3 : jacPiece e6T 78 50 39 52 = true := by decide +kernel

theorem e6J_50_4 : jacPiece e6T 78 50 52 65 = true := by decide +kernel

theorem e6J_50_5 : jacPiece e6T 78 50 65 78 = true := by decide +kernel

theorem e6J_51_4 : jacPiece e6T 78 51 52 65 = true := by decide +kernel

theorem e6J_51_5 : jacPiece e6T 78 51 65 78 = true := by decide +kernel

end VOA.AffineGeneral.SCLie
