/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityRhoD

/-!
# The Lee–Yang endpoint with `GhostConjBE` discharged

* `leeYang_gradedUnitary_of_affine_ghostConjD` — **Affine GU ⇒ Lee–Yang GU** with the
  skewness clause `GhostConjBE` **proved** (`ghostConjBE_proved`); remaining: `hB`, `hD` and the
  five downstream inputs.
* `leeYang_gradedUnitary_of_affine_ghostCubic` — the same with `hD : GhostConjRhoD` replaced
  by the ghost-only identity `hC : GhostCubicConj` (`ghostConjRhoD_of_cubic`).

Everything here is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-- **Affine GU ⇒ Lee–Yang GU with `GhostConjBE` proved.** `#print axioms`-clean, conditional
on: `hA` (the hypothesis), `hB`, `hD` (`GhostConjRhoD`) and the downstream `symbols`,
`character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_ghostConjD
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) (hD : GhostConjRhoD)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA hD ghostConjBE_proved).pkg hB).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_ghostConj hA hB hD ghostConjBE_proved symbols character
    vacuumNormalized creationAdjoint wordsReal

/-- **Affine GU ⇒ Lee–Yang GU from the ghost-only cubic identity.** `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB`, `hC` (`GhostCubicConj`, a statement about the
three-pair ghost system only) and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_ghostCubic
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) (hC : GhostCubicConj)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA (ghostConjRhoD_of_cubic hC) ghostConjBE_proved).pkg hB).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_ghostConjD hA hB (ghostConjRhoD_of_cubic hC) symbols character
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
