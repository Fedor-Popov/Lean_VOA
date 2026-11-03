/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTConjIdentityCubicB
import VOA.Examples.BRSTConjIdentityEndpoint

/-!
# `GhostConjRhoD` and `GhostConjBE` proved; the endpoint without them

* `kpZero_proved : KpZero` — the step operators vanish (`Kp_c_zero`, `Kp_b_zero`);
* `ghostCubicConj_proved : GhostCubicConj`;
* `ghostConjRhoD_proved : GhostConjRhoD`;
* `leeYang_gradedUnitary_of_affine_bgConj` — **Affine GU ⇒ Lee–Yang GU**, conditional only on
  `hA` (the hypothesis), `hB` and the five downstream inputs; both Beem–Garner identities of the
  ghost conjugation are theorems.

Everything is proved outright (no `hA`).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-- **The step operators vanish.** -/
theorem kpZero_proved : KpZero := by
  intro N a p hp W hW y hy hC
  obtain ⟨j, e⟩ := p
  match e, hp, hW with
  | 0, _, hW =>
    have hk : 1 ≤ j + 1 := by omega
    have h := Kp_b_zero N a hk (W := W) (by simpa [ghModeWt, ghWt] using hW) hy hC
    simpa using h
  | 1, hp, hW =>
    have hk : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact absurd rfl hp
      · exact h
    exact Kp_c_zero N a hk (W := W) (by simpa [ghModeWt, ghWt] using hW) hy hC

/-- **The ghost-only identity for the cubic charge.** -/
theorem ghostCubicConj_proved : GhostCubicConj := ghostCubicConj_of_Kp kpZero_proved

/-- **`GhostConjRhoD` is proved outright** (no hypothesis; in particular no `hA`). -/
theorem ghostConjRhoD_proved : GhostConjRhoD := ghostConjRhoD_of_cubic ghostCubicConj_proved

/-- **Affine GU ⇒ Lee–Yang GU with the Beem–Garner ghost conjugation fully constructed.**
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for
the canonical pair) and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgConj
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_ghostConj hA hB ghostConjRhoD_proved ghostConjBE_proved symbols
    character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
