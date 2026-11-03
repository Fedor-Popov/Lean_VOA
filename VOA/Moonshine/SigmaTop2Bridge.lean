/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTopOffdiag
import VOA.Moonshine.ZhuGenerated

/-!
# (R-top) bridge: `SigmaTop.G2 = SigmaExist.weightTwo`

The letter set `G2 = {g | (g : V_Λ⁺) ∈ (V_Λ⁺)₂}` of the `SigmaTop*` reductions and the set
`weightTwo = {g | g ∈ (V₀⁺)₂}` of R-gen coincide *definitionally* (the grading of `V₀⁺` is the
restriction of that of `V_Λ⁺`, `VOASubalgebra.toVOA`).  Hence the `ZhuGenerated G2` hypothesis of
`topSigmaV3_of_eigen`, `topSigmaTT_of_eigen` (and of everything downstream) is discharged by
`Moonshine.zhuGenerated_weightTwo`.

## Main results
* `G2_eq_weightTwo : G2 = weightTwo` (`rfl`).
* `zhuGenerated_G2 : ZhuGenerated G2` — unconditional, no `VOA.pbw`.

## Status
`sorry`-free; `#print axioms zhuGenerated_G2`: `[propext, Classical.choice, Quot.sound]`.
Imported by the umbrella `VOA/Moonshine.lean`.
-/

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist

/-- The two weight-two letter sets agree definitionally. -/
theorem G2_eq_weightTwo : G2 = weightTwo := rfl

/-- **R-gen for the `SigmaTop` letter set**. -/
theorem zhuGenerated_G2 : ZhuGenerated G2 := zhuGenerated_weightTwo

end VOA.Moonshine.SigmaTop
