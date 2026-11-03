/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LevelOneUnitaryPositivity
import VOA.Examples.HarmonicMetricEndpoint

/-!
# The endpoint with unitarity of `L_1(sl₂)` discharged

`leeYang_gradedUnitary_of_affine_levelOne` — **Affine GU ⇒ Lee–Yang GU**, i.e.
`leeYang_gradedUnitary_of_affine_harmonic` with its input `hB : Unitary bForm bRealStructure`
supplied by the proved `LevelOneUnitary.bUnitary`.  `#print axioms`-clean, conditional on `hA`
(the hypothesis: graded unitarity of the boundary affine `L_{-4/3}(sl₂)`) and the two remaining
inputs `symbols` and `character`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity

noncomputable section

/-- **Affine GU ⇒ Lee–Yang GU, with unitarity of `L_1(sl₂)` proved.**
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `symbols`, `character`. -/
theorem leeYang_gradedUnitary_of_affine_levelOne
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg
          LevelOneUnitary.bUnitary).sp2))
    (character : LeeYangPBWCharacter) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_harmonic hA LevelOneUnitary.bUnitary symbols character

end

end VOA.ConcreteHodge
