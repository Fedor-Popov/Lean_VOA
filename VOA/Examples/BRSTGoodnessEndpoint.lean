/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessDifferential

/-!
# The Lee–Yang endpoint with the zero-mode and goodness inputs discharged

`leeYang_gradedUnitary_of_affine_ghost` (`ConcreteGoodGenerators`) took five open inputs about
the actual operators: `hG0 : GhostCurrentZeroPreserve`, `hb0 : AntighostZeroShift`,
`hD : RelativeDifferentialGood (ghostRGrading w)`, `hK : InterpretedKahlerAnticomm …` and the
creation test. The first three are theorems:

* `ghostCurrentZeroPreserve`, `antighostZeroShift` (`BRSTGoodnessGhostCurrent`,
  `BRSTGoodnessFock`) — unconditional;
* `relativeDifferentialGood_of_affine hA hB w hw` (`BRSTGoodnessDifferential`) — from the
  hypothesis `hA` and the unitarity `hB` of `L_1(sl₂)`, both already inputs of the endpoint.

`leeYang_gradedUnitary_of_affine_good` is the endpoint with those three inputs removed.
-/

namespace VOA.ConcreteHodge

open LeeYangTransferAssembly LeeYangShortcut Sl2CosetConcrete Sl2SemiInfinite
open VirGradedUnitarity LeeYang VOA.VertexOperatorAlgebra VOA.GradedUnitaryCohomology

noncomputable section

/-- The proved zero-mode homogeneity for the concrete ghost grading. -/
abbrev hZproved (w : Finset ModeIdx → ℝ) : ZeroModesPreserve (ghostRGrading w) :=
  zeroModesPreserve_concrete w ghostCurrentZeroPreserve antighostZeroShift

/-- **Affine GU ⇒ Lee–Yang GU**, with the ghost zero-mode statements and Beem–Garner goodness
of the actual differential proved. `#print axioms`-clean, conditional on the listed inputs:
`hA` (the hypothesis), `hB`, a positive ghost weight `w`, the Kähler relation `hK` for the
derived second differential, and the downstream inputs `R`, `symbols`, `character`, `creation`,
`vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_good
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) (hZproved w)
      (relativeDifferentialGood_of_affine hA hB w hw))
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood (interpretedGoodGeometry (ghostRGrading w)
      hA hB (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        n hp))
    (symbols : LeadingInvariantSymbolDimension (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK))
    (character : LeeYangPBWCharacter)
    (creation : ∀ hp, InterpretedCreation w hw hA hB (hZproved w)
      (relativeDifferentialGood_of_affine hA hB w hw) hK hp)
    (vacuumNormalized : HarmonicVacuumNormalized (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R))
    (creationAdjoint : HarmonicCreationAdjoint (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R))
    (wordsReal : HarmonicWordsReal (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_ghost hA hB w hw ghostCurrentZeroPreserve antighostZeroShift
    (relativeDifferentialGood_of_affine hA hB w hw) hK R symbols character creation
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
