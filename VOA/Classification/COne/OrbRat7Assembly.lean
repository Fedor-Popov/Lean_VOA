/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbRat4Telescope
import VOA.Classification.COne.OrbRat6Heis

/-!
# The tetrahedral model after the V₈ telescope and the character table

With `OrbRat4.telescope_V8_holds` and `OrbRat6.cubicZhuCharacterTable_holds` proved, the direct
`A₄` route to rationality rests on `C₂`-cofiniteness, `CubicZhuDimensionBound` and
`CubicNonVacuumPairs` only.
-/

namespace VOA.Classification.COne.OrbRat7

open VOA VertexOperatorAlgebra OrbRat2

/-- `CubicVacuumTelescope` from `C₂` and the Zhu dimension bound. -/
theorem cubicVacuumTelescope_of_dim (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) : CubicVacuumTelescope :=
  OrbRat4.cubicVacuumTelescope_of_zhu hC2 hdim OrbRat6.cubicZhuCharacterTable_holds

/-- Rationality-from-`C₂` for the tetrahedral model from the Zhu dimension bound and the
non-vacuum resonant pairs. -/
theorem cubicModelRationalOfC2_of_dim (hdim : CubicZhuDimensionBound)
    (hnv : CubicNonVacuumPairs) : CubicModelRationalOfC2 :=
  OrbRat4.cubicModelRationalOfC2_of_zhu hdim OrbRat6.cubicZhuCharacterTable_holds hnv

end VOA.Classification.COne.OrbRat7
