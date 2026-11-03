/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbC2dExceptional
import VOA.Classification.COne.OrbPrimEquiv
import VOA.Classification.COne.OrbC2hFinal

/-!
# B2 after the Dong–Jiang span theorem

With `OrbPrim.tetrahedralVirasoroSpan_holds`, the C₂ input B2 of the Gannon–Rayhaun converse
rests on the tetrahedral mode decomposition (the corrected Dong–Jiang relations) and the
octahedral involution input only.
-/

namespace VOA.Classification.COne.OrbB2

open VOA OrbC2b OrbC2c OrbC2d

/-- B2 from the tetrahedral mode decomposition and the octahedral involution input. -/
theorem solvableExceptionalOrbifoldC2Fact_of_two_inputs (hr : TetrahedralModeDecomposition)
    (hI : InvolutionMovingPairSpan) : SolvableExceptionalOrbifoldC2Fact :=
  solvableExceptionalOrbifoldC2Fact_of_three_inputs OrbPrim.tetrahedralVirasoroSpan_holds hr hI

/-- B2 from the octahedral involution input alone: the tetrahedral span
(`OrbPrim.tetrahedralVirasoroSpan_holds`) and mode decomposition (`OrbC2h.tetrahedralModeDecomposition`)
are proved. -/
theorem solvableExceptionalOrbifoldC2Fact_of_involution (hI : InvolutionMovingPairSpan) :
    SolvableExceptionalOrbifoldC2Fact :=
  solvableExceptionalOrbifoldC2Fact_of_two_inputs OrbC2h.tetrahedralModeDecomposition hI

end VOA.Classification.COne.OrbB2
