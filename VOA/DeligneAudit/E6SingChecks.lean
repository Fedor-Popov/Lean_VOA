/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E6LieDataTab

/-!
# E₆ at level `-3`: the weight-two highest-weight singular vector (Boolean checks)

`e6hw = J^{29}J^{41} + J^{32}J^{40} - J^{35}J^{39} + J^{37}J^{38}` (all `(-1)` modes on `|0⟩`; the four pairs
commute), the highest-weight vector of `V(θ) ⊂ Sym² 𝔢₆` at weight two.  `e6hw_q1`, `e6hw_q2`: every positive
current mode kills it at `k = -3` (`q1OK`: weight one, `q2OK`: vacuum).
-/

set_option maxRecDepth 100000

namespace VOA.AffineGeneral.SCLie

/-- The highest-weight singular vector, as `(coefficient, a, b)`. -/
def e6hw : List (ℤ × Fin 78 × Fin 78) := [(1, 29, 41), (1, 32, 40), (-1, 35, 39), (1, 37, 38)]

theorem e6hw_q1 : q1OK e6T e6Gm (-3) e6hw = true := by decide +kernel

theorem e6hw_q2 : q2OK e6T e6Gm (-3) e6hw = true := by decide +kernel

end VOA.AffineGeneral.SCLie
