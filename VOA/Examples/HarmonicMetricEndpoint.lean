/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.HarmonicMetricVacuum
import VOA.Examples.HarmonicMetricReal
import VOA.Examples.HarmonicMetricAdjoint

/-!
# The three harmonic-metric inputs are theorems

* `harmonicVacuumNormalized_proved`, `harmonicCreationAdjoint_proved`,
  `harmonicWordsReal_proved` — the three inputs of `leeYang_gradedUnitary_of_affine_bgConj`, for
  the concrete endpoint complex, proved outright from the bridge (`HarmonicMetricBridge`) and the
  three statements on explicit representatives (`repVacuumNormalized_proved`,
  `repCreationAdjoint_proved`, `repWordsReal_proved`);
* `leeYang_gradedUnitary_of_affine_harmonic` — **Affine GU ⇒ Lee–Yang GU**, conditional only on
  `hA` (the hypothesis), `hB`, `symbols`, `character`.

Everything is proved outright (no `hA` used in the three inputs beyond indexing the complex).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity

noncomputable section

theorem harmonicVacuumNormalized_proved
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) :
    HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0) :=
  harmonicVacuumNormalized_of_rep _ repVacuumNormalized_proved

theorem harmonicCreationAdjoint_proved
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) :
    HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0) :=
  harmonicCreationAdjoint_of_rep _ fun i _ _ x y _ _ => repCreationAdjoint_proved i x y

theorem harmonicWordsReal_proved
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) :
    HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0) :=
  harmonicWordsReal_of_rep _ fun _ w _ => Subtype.ext (repWordsReal_proved w)

/-- **Affine GU ⇒ Lee–Yang GU with all three harmonic-metric inputs proved.**
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for
the canonical pair), `symbols`, `character`. -/
theorem leeYang_gradedUnitary_of_affine_harmonic
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2))
    (character : LeeYangPBWCharacter) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_reps hA hB symbols character repVacuumNormalized_proved
    repCreationAdjoint_proved repWordsReal_proved

end

end VOA.ConcreteHodge
