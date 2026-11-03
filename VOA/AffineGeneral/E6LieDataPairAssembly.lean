/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLieData

/-! Symbolic assembly of fixed-column dual-pairing checks. -/
namespace VOA.AffineGeneral.SCLie

theorem e6_pairChunk_of_rows (N : ℕ) (Gm : List (ℕ × ℕ × ℤ))
    (dl : ℕ → List (ℕ × ℤ)) (D : ℕ → ℤ) (lo hi : ℕ)
    (h : ∀ j, lo ≤ j → j < hi →
      (decide (D j ≠ 0) && inRange N (dl j) &&
        (List.range N).all (fun i => formV Gm [(i, 1)] (dl j) ==
          if i = j then D j else 0)) = true) :
    pairChunk N Gm dl D lo hi = true := by
  apply List.all_eq_true.mpr
  intro j hj
  obtain ⟨hlo, hlen⟩ := List.mem_range'_1.mp hj
  exact h j hlo (by omega)

end VOA.AffineGeneral.SCLie
