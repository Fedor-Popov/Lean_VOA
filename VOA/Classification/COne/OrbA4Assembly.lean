/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbB2Assembly
import VOA.Classification.COne.OrbOctaMain
import VOA.Classification.COne.OrbRat8Vir

/-!
# `C₂`-cofiniteness of `V₂^{A₄}`, and what remains of B2 and B3

The tetrahedral span (`OrbPrim.tetrahedralVirasoroSpan_holds`) and the tetrahedral mode
decomposition (`OrbC2h.tetrahedralModeDecomposition`) give `C₂`-cofiniteness of `V₂^{A₄}` with no
hypotheses; it transfers to the cubic model used by the rationality argument.  B2 then rests on
the octahedral nilpotence `OrbOcta.OctahedralConformalNilpotent`, and rationality of the cubic
model on the Zhu dimension bound and the two non-vacuum residuals.
-/

namespace VOA.Classification.COne.OrbA4

open VOA VertexOperatorAlgebra OrbC2b OrbC2c OrbRat2

/-- **`V₂^{A₄}` is `C₂`-cofinite** (Dong–Jiang; no hypotheses). -/
theorem tetra_c2Cofinite_holds : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_state_inputs OrbPrim.tetrahedralVirasoroSpan_holds
    OrbC2h.tetrahedralModeDecomposition

/-- The cubic model `(V₂^{V₄})^{ℤ/3} ≅ V₂^{A₄}` is `C₂`-cofinite. -/
theorem cubicModel_c2Cofinite_holds : C2Cofinite cubicModel := by
  obtain ⟨e, he, _⟩ := tetra_cubic_iso
  exact ConverseUniverse.c2Cofinite_of_iso e he tetra_c2Cofinite_holds

/-- B2 from the octahedral nilpotence alone. -/
theorem solvableExceptionalOrbifoldC2Fact_of_octaNilpotent
    (hN : OrbOcta.OctahedralConformalNilpotent) : SolvableExceptionalOrbifoldC2Fact :=
  OrbB2.solvableExceptionalOrbifoldC2Fact_of_involution
    (OrbOcta.involutionMovingPairSpan_of_octahedralConformalNilpotent hN)

/-- Rationality of the cubic model from the Zhu dimension bound and the two non-vacuum
residuals (`C₂` is proved). -/
theorem cubicModel_admissiblyRational_of_residuals (hdim : CubicZhuDimensionBound)
    (h41 : OrbRat8.TopCyclicFourOneResidual)
    (h94 : OrbRat8.TopCyclicVanishing cubicModel (1 / 4) (9 / 4)) :
    AdmissiblyRational cubicModel :=
  OrbRat8.cubicModelRationalOfC2_of_residuals hdim h41 h94 cubicModel_c2Cofinite_holds

end VOA.Classification.COne.OrbA4
