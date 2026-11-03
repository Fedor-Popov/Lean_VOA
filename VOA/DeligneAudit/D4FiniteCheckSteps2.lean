/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteCheckSteps

/-!
# D₄ finite identity, kernel checkpoints III: Demazure steps 6–9 of `π_{s_θ}`

`d4L6, …, d4L9` are literal term lists, each re-verified by the kernel as one Demazure step of its
predecessor (a few seconds each).
-/

namespace VOA.DeligneAudit.D4Finite

open Gen

set_option maxRecDepth 100000

noncomputable def d4L6 : UList := d4_precompute% stepsU 6
noncomputable def d4L7 : UList := d4_precompute% stepsU 7
noncomputable def d4L8 : UList := d4_precompute% stepsU 8
noncomputable def d4L9 : UList := d4_precompute% stepsU 9

theorem d4L6_eq : demU (d4Roots.getD 1 []) d4L5 = d4L6 := by
  decide +kernel

theorem d4L7_eq : demU (d4Roots.getD 2 []) d4L6 = d4L7 := by
  decide +kernel

theorem d4L8_eq : demU (d4Roots.getD 0 []) d4L7 = d4L8 := by
  decide +kernel

theorem d4L9_eq : demU (d4Roots.getD 1 []) d4L8 = d4L9 := by
  decide +kernel

theorem evalU_d4L9 : evalU d4L9 = piSThetaU d4QU := by
  have h1 : evalU d4L1 = demazureU (d4Roots.getD 1 []) (evalU d4L0) := by rw [← d4L1_eq, evalU_demU]
  have h2 : evalU d4L2 = demazureU (d4Roots.getD 0 []) (evalU d4L1) := by rw [← d4L2_eq, evalU_demU]
  have h3 : evalU d4L3 = demazureU (d4Roots.getD 2 []) (evalU d4L2) := by rw [← d4L3_eq, evalU_demU]
  have h4 : evalU d4L4 = demazureU (d4Roots.getD 1 []) (evalU d4L3) := by rw [← d4L4_eq, evalU_demU]
  have h5 : evalU d4L5 = demazureU (d4Roots.getD 3 []) (evalU d4L4) := by rw [← d4L5_eq, evalU_demU]
  have h6 : evalU d4L6 = demazureU (d4Roots.getD 1 []) (evalU d4L5) := by rw [← d4L6_eq, evalU_demU]
  have h7 : evalU d4L7 = demazureU (d4Roots.getD 2 []) (evalU d4L6) := by rw [← d4L7_eq, evalU_demU]
  have h8 : evalU d4L8 = demazureU (d4Roots.getD 0 []) (evalU d4L7) := by rw [← d4L8_eq, evalU_demU]
  have h9 : evalU d4L9 = demazureU (d4Roots.getD 1 []) (evalU d4L8) := by rw [← d4L9_eq, evalU_demU]
  rw [h9, h8, h7, h6, h5, h4, h3, h2, h1, evalU_d4L0]
  rfl

end VOA.DeligneAudit.D4Finite
