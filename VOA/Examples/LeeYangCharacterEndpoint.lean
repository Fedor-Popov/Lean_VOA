import VOA.Examples.LeeYangCharacterReduction
import VOA.Examples.LevelOneUnitaryEndpoint

/-!
# The endpoint with the refined character replaced by the classical lower bound

`leeYang_gradedUnitary_of_affine_levelOne_rr` — **Affine GU ⇒ Lee–Yang GU**, with the
refined PBW-length character `LeeYangPBWCharacter` replaced by the strictly weaker-looking
(and, by `leeYangPBWCharacter_iff_lowerBound`, equivalent) classical statement
`LeeYangRRLowerBound`: `#{gap-two partitions of N} ≤ dim L(-22/5,0)_N`.

The length-refinement and the upper bound are theorems (gap-two straightening, proved);
only the total-dimension lower bound remains.  `#print axioms`-clean, conditional on `hA`
(the hypothesis), `symbols`, and `lower`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity

noncomputable section

/-- **Affine GU ⇒ Lee–Yang GU**, conditional on `hA` (the hypothesis), `symbols`, and the
classical Rogers–Ramanujan lower bound `lower`. -/
theorem leeYang_gradedUnitary_of_affine_levelOne_rr
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA LevelOneUnitary.bUnitary bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg
          LevelOneUnitary.bUnitary).sp2))
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_levelOne hA symbols
    (LeeYangCharacter.leeYangPBWCharacter_iff_lowerBound.mpr lower)

end

end VOA.ConcreteHodge
