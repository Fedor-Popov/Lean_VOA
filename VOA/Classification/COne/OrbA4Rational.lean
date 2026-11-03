/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbA4Assembly
import VOA.Classification.COne.OrbSglMain

/-!
# Rationality of the tetrahedral model: the two non-vacuum residuals

`C₂` (`OrbA4.cubicModel_c2Cofinite_holds`), the character table, the vacuum telescope and the Zhu
dimension bound (`OrbSgl.cubicZhuDimensionBound_holds`) are proved.  Rationality of the cubic model
`(V₂^{V₄})^{ℤ/3} ≅ V₂^{A₄}` rests only on the two non-vacuum resonant residuals.
-/

namespace VOA.Classification.COne.OrbA4

open VOA VertexOperatorAlgebra OrbRat2

/-- Rationality of the tetrahedral model from the two non-vacuum residuals alone. -/
theorem cubicModel_admissiblyRational_of_topCyclic (h41 : OrbRat8.TopCyclicFourOneResidual)
    (h94 : OrbRat8.TopCyclicVanishing cubicModel (1 / 4) (9 / 4)) :
    AdmissiblyRational cubicModel :=
  cubicModel_admissiblyRational_of_residuals OrbSgl.cubicZhuDimensionBound_holds h41 h94

end VOA.Classification.COne.OrbA4
