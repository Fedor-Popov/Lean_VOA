/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainConverse
import VOA.Classification.COne.OrbOctaRCFinal

/-!
# The converse of Gannon–Rayhaun after B2

`SolvableExceptionalOrbifoldC2Fact` (B2: `C₂`-cofiniteness of `V₂^{A₄}` and `V₂^{S₄}`) is proved
(`solvableExceptionalOrbifoldC2Fact_holds`).  The converse then rests on three inputs: Xu's
icosahedral
relations (B4), rationality from `C₂` for the finite orbifolds (B3), and positivity of twisted
weights (B5).
-/

namespace VOA.Classification.COne

/-- **The converse of Gannon–Rayhaun**, conditional only on B3, B4, B5 (B2 is proved). -/
theorem gannonRayhaunConverse_of_B3_B4_B5 (hXu : XuIcosahedralPoissonRelations)
    (hRat : FiniteV2OrbifoldRationalOfC2Fact) (hPU : ExceptionalOrbifoldPositiveWeightsFact) :
    GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_exceptional solvableExceptionalOrbifoldC2Fact_holds hXu hRat hPU

end VOA.Classification.COne
