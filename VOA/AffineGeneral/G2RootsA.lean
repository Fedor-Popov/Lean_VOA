/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2Table

set_option linter.style.longLine false

/-!
# Cheap root-table checks for `𝔤₂`
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

theorem g2RC_inRange : ∀ α, inRange 14 (hL g2T g2Data α) = true := by decide +kernel
theorem g2RC_diag : ∀ α, g2Data.pairT α α ≠ 0 := by decide +kernel
theorem g2RC_M : ∀ α, zeroL (hL g2T g2Data α ++ scale (-1)
    ((List.finRange g2Data.r).flatMap fun i => scale (g2Data.M α i) (hL g2T g2Data (g2Data.simple i)))) = true := by decide +kernel
theorem g2RC_Q : ∀ i j, ∑ k, (g2Data.pairT (g2Data.simple i) (g2Data.simple k) : ℚ) * g2Data.Q k j = if i = j then 1 else 0 := by decide +kernel
theorem g2RC_conn : ∀ β, β = g2Data.base ∨ ∃ γ, g2Data.dist γ < g2Data.dist β ∧ g2Data.pairT γ β ≠ 0 := by decide +kernel
theorem g2RC_span : ∀ k : Fin 14, (∃ β, g2Data.rootIdx β = k) ∨
    ∃ i, zeroL (hL g2T g2Data (g2Data.simple i) ++ [((k : ℕ), 1)]) = true ∨
      zeroL (hL g2T g2Data (g2Data.simple i) ++ [((k : ℕ), -1)]) = true := by decide +kernel

end VOA.AffineGeneral.SCLie
