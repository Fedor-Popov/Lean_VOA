/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.F4Table

set_option linter.style.longLine false

/-!
# Cheap root-table checks for `𝔣₄`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem f4RC_inRange : ∀ α, inRange 52 (hL f4T f4Data α) = true := by decide +kernel
theorem f4RC_diag : ∀ α, f4Data.pairT α α ≠ 0 := by decide +kernel
theorem f4RC_M : ∀ α, zeroL (hL f4T f4Data α ++ scale (-1)
    ((List.finRange f4Data.r).flatMap fun i => scale (f4Data.M α i) (hL f4T f4Data (f4Data.simple i)))) = true := by decide +kernel
theorem f4RC_Q : ∀ i j, ∑ k, (f4Data.pairT (f4Data.simple i) (f4Data.simple k) : ℚ) * f4Data.Q k j = if i = j then 1 else 0 := by decide +kernel
theorem f4RC_conn : ∀ β, β = f4Data.base ∨ ∃ γ, f4Data.dist γ < f4Data.dist β ∧ f4Data.pairT γ β ≠ 0 := by decide +kernel
theorem f4RC_span : ∀ k : Fin 52, (∃ β, f4Data.rootIdx β = k) ∨
    ∃ i, zeroL (hL f4T f4Data (f4Data.simple i) ++ [((k : ℕ), 1)]) = true ∨
      zeroL (hL f4T f4Data (f4Data.simple i) ++ [((k : ℕ), -1)]) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
