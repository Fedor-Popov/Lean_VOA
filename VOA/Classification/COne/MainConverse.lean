/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusRat6Final
import VOA.Classification.COne.PlusC2Final
import VOA.Classification.COne.PlusUnitaryFinal
import VOA.Classification.COne.ExceptionalOrbifoldNice

/-!
# The converse of Gannon–Rayhaun: only the exceptional orbifolds remain

Gannon–Rayhaun Proposition 3.2 (`GannonRayhaunConverse`): every VOA in the list is nice and has
central charge `1`.  The lattice family `V_{2m}` and the whole family `V_{2m}⁺` are proved:
`V_{2m}⁺` is `C₂`-cofinite (`v2mPlusC2CofiniteFactGe2_holds`), pseudo-unitary
(`v2mPlusPseudoUnitaryFactGe2_holds`) and rational for every `m ≥ 2`
(`v2mPlusRationalFactGe2_holds`, by a uniform version of Abe's splitting argument).

The converse is therefore CONDITIONAL only on the four inputs about the exceptional orbifolds
`V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}`: `SolvableExceptionalOrbifoldC2Fact` (B2),
`XuIcosahedralPoissonRelations` (B4), `FiniteV2OrbifoldRationalOfC2Fact` (B3) and
`ExceptionalOrbifoldPositiveWeightsFact` (B5).
-/

namespace VOA.Classification.COne

/-- **`V_{2m}⁺` is nice for every `m ≥ 1`** (unconditional). -/
theorem V2mPlus_nice (m : ℕ) (hm : 1 ≤ m) : Nice (V2mPlus m hm) :=
  nice_V2mPlus_of_rational_pseudoUnitary v2mPlusRationalFactGe2_holds
    v2mPlusPseudoUnitaryFactGe2_holds m hm

/-- **The converse of Gannon–Rayhaun, conditional only on the four exceptional-orbifold
inputs** (the `V_{2m}` and `V_{2m}⁺` clauses are proved). -/
theorem gannonRayhaunConverse_of_exceptional (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : FiniteV2OrbifoldRationalOfC2Fact)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_exceptional_inputs v2mPlusRationalFactGe2_holds hSolv hXu hRat hPU

end VOA.Classification.COne
