/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FiniteCheckQ

/-!
# D₄ finite identity, kernel checkpoints II: Demazure steps 1–5 of `π_{s_θ}`

`d4L1, …, d4L5` are literal term lists, each re-verified by the kernel as one Demazure step of its
predecessor (a few seconds each).
-/

namespace VOA.DeligneAudit.D4Finite

open Gen

set_option maxRecDepth 100000

/-! ## Checkpoints along `π_{s_θ}` (in the `(q, u, t, z)` world) -/

noncomputable def d4L1 : UList := d4_precompute% stepsU 1
noncomputable def d4L2 : UList := d4_precompute% stepsU 2
noncomputable def d4L3 : UList := d4_precompute% stepsU 3
noncomputable def d4L4 : UList := d4_precompute% stepsU 4
noncomputable def d4L5 : UList := d4_precompute% stepsU 5

theorem d4L1_eq : demU (d4Roots.getD 1 []) d4L0 = d4L1 := by
  decide +kernel

theorem d4L2_eq : demU (d4Roots.getD 0 []) d4L1 = d4L2 := by
  decide +kernel

theorem d4L3_eq : demU (d4Roots.getD 2 []) d4L2 = d4L3 := by
  decide +kernel

theorem d4L4_eq : demU (d4Roots.getD 1 []) d4L3 = d4L4 := by
  decide +kernel

theorem d4L5_eq : demU (d4Roots.getD 3 []) d4L4 = d4L5 := by
  decide +kernel

end VOA.DeligneAudit.D4Finite
