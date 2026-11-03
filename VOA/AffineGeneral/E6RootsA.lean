/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# Cheap root-table checks for `𝔢₆`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem e6RC_inRange : ∀ α, inRange 78 (hL e6T e6Data α) = true := by decide +kernel
theorem e6RC_diag : ∀ α, e6Data.pairT α α ≠ 0 := by decide +kernel
theorem e6RC_M : ∀ α, zeroL (hL e6T e6Data α ++ scale (-1)
    ((List.finRange e6Data.r).flatMap fun i => scale (e6Data.M α i) (hL e6T e6Data (e6Data.simple i)))) = true := by decide +kernel
theorem e6RC_Q : ∀ i j, ∑ k, (e6Data.pairT (e6Data.simple i) (e6Data.simple k) : ℚ) * e6Data.Q k j = if i = j then 1 else 0 := by decide +kernel
theorem e6RC_conn : ∀ β, β = e6Data.base ∨ ∃ γ, e6Data.dist γ < e6Data.dist β ∧ e6Data.pairT γ β ≠ 0 := by decide +kernel
theorem e6RC_span : ∀ k : Fin 78, (∃ β, e6Data.rootIdx β = k) ∨
    ∃ i, zeroL (hL e6T e6Data (e6Data.simple i) ++ [((k : ℕ), 1)]) = true ∨
      zeroL (hL e6T e6Data (e6Data.simple i) ++ [((k : ℕ), -1)]) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
