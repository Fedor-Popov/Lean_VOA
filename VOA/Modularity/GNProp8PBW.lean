/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNProp8Closure
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom

/-!
# The canonical-PBW leaf of the pinned modularity theorem

This leaf specializes the explicit regular-bottom projection in
`zhuModularity_pinned_of_C2Cofinite` to `voaPBWBottomProjection`, i.e. to the theorem
`VOA.pbw : PBWPrinciple`.  Its `#print axioms` is Lean's three
standard axioms; the reusable explicit-projection theorem does not use `VOA.pbw`.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pinned Zhu modularity with the regular-bottom projection supplied by the PBW theorem
`VOA.pbw`.**

No `VacuumGradeZero` or bottom-simplicity hypothesis (both are automatic: `vacuumGradeZero_holds`,
`isSimpleAMod_lowestAMod_of_semisimple` from `hss` and `Pr`). -/
theorem zhuModularity_pinned_of_C2Cofinite_voaPBW [Finite (Φ W)]
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hcard : Fintype.card ι = Nat.card (Φ W))
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hsep : ∀ j k : ι, j ≠ k → h j = h k →
      IsEmpty (AModEquiv W (lowestAMod (hcw j).2) (lowestAMod (hcw k).2))) :
    ∃ D : ModularData W ι, D.Mfam = Mfam ∧ D.h = h ∧ ZhuModularityAnalytic D :=
  zhuModularity_pinned_of_C2Cofinite Mfam h hC2 hss
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W)))
    hcard hcw hsep

end VOA
