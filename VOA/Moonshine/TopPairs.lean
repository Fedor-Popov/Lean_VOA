/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TopPairsCore
import VOA.Moonshine.MainTopPairs

/-!
# `TopPairs` for the explicit triality data, and the Moonshine module

`TopPairsCore.top_pairs0` proves `Θ₀(o(v)Φ₀b) = o(b)Φ₀v` on `(V₃⁺)₂` for the unnormalised data of
`SigmaAssemble`.  The normalised data `mkData c⋆ ε` has `Φ = c⋆Φ₀`, `Θ = εΘ₀`; both sides of
`FZKey.TopPairs` scale by `c⋆`, so `TopPairs` holds for **`ε = +1`** (`topPairs_one`).  (For
`ε = −1` it would force `Θ₀(o(x_n)Φ₀x_n) = 0`; analysis only, not formalised.)

Feeding this into `Moonshine.moonshine_of_topPairs` (`MainTopPairs.lean`) gives the Moonshine
module with all definition-of-done targets.

## Main results
* `topPairs_one : FZKey.TopPairs (mkData cStar0 1 _ _)`.
* `moonshine : ∃ V : VertexOperatorAlgebra Vnat, V.Y = Ynat … ∧ V.vacuum = vacNat ∧
  V.conformalVector = omegaNat ∧ V.centralCharge = 24 ∧ V.grading 1 = ⊥ ∧
  finrank (V.grading 2) = 196884 ∧ (graded dimensions = coefficients of `J`) ∧ V.IsSimple`.

## Status
`sorry`-free; **no hypotheses**.
`#print axioms moonshine`, `topPairs_one`:
`[propext, Classical.choice, Quot.sound]` — not even `VOA.pbw`.  Imported by the umbrella
`VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open SigmaAssemble TopPairs

/-- **`TopPairs` holds for the explicit triality data with `ε = +1`.** -/
theorem topPairs_one :
    FZKey.TopPairs (mkData cStar0 1 (c_ne_of_norm cStar0_norm) (by norm_num)) := by
  intro v hv b hb
  change ((1 : ℂ) • Θ0) (mode (plusModule.YM v) 1 ((cStar0 • Φ0) b))
    = mode (plusModule.YM b) 1 ((cStar0 • Φ0) v)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, one_smul,
    mode_smul_right, mode_smul_right, map_smul, top_pairs0 hv hb]

/-- **The Moonshine module `V♮`**, unconditionally: a vertex operator algebra structure on
`Vnat` (the genuine block map `Ynat`), central charge `24`, `V₁ = 0`, `dim V₂ = 196884`, graded
dimension `J(q)`, simple. -/
theorem moonshine :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_topPairs (by norm_num) topPairs_one

end VOA.Moonshine
