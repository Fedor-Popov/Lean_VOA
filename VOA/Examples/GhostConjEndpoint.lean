/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GhostConjJ0

/-!
# The Lee–Yang endpoint with the ghost conjugation constructed

With the ghost factor constructed and proved (`bgGhostData`, `GhostConjFock` + `GhostConjJ0`), the
proved matter factor (`bgMatterData`), `κ = 1` and the corrected skewness constant
(`GhostConjChain`), what remains of the Beem–Garner package are two concrete statements about the
BRST differential:

* `GhostConjRhoD` — `ρ 𝐐 = (-1)^{gh} [Λ, 𝐐] ρ` on relative states, `ρ = ρ_M ⊗ ρ_G`;
* `GhostConjBE` — `B([Λ, 𝐐] u, v) = i (-1)^{gh u} B(u, [Λ, 𝐐] v)` on relative states,
  `B = B_M ⊗ B_G`.

Both are hypotheses here; they do not mention `hA`. Both are since proved outright:
`ghostConjRhoD_proved` (`BRSTConjIdentityProved.lean`), `ghostConjBE_proved`
(`BRSTConjIdentityBE.lean`). Both were first verified numerically to machine precision on a
truncated model of the complex with the universal matter factors (relative weights `2, 3, 4`;
operator identities there descend to the simple quotients; see the layer report).

* `bgGhostRemainderI` — the corrected remainder from these two statements;
* `leeYang_gradedUnitary_of_affine_ghostConj` — **Affine GU ⇒ Lee–Yang GU**.

**Why not `BGGhostRemainder`.** The original remainder (`BGPackageBFactor`) uses the skewness
constant `-(-1)^{gh}`; together with `ρ² = s` this is unsatisfiable on the actual complex
(numerical certificate at weight `2`: `ρ_D` forces `ρ²` on one-ghost states to be `κ²/|κ|²` times
`ρ²` on the vacuum sector, so `ρ² = s` forces `κ` real, and then `B_E` fails for every real `κ`
even with the two-ghost block of `B_G` left free). The machine-checked statement of this obstruction
is **not** part of this layer.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-- The product conjugation `ρ_M ⊗ ρ_G` on the BRST space. -/
def ghConjBRST : BRSTSpace →ₗ⋆[ℂ] BRSTSpace :=
  TensorProduct.map (matterRho bRealStructure) ghostConj

/-- The product bilinear form `B_M ⊗ B_G` on the BRST space. -/
def ghBBRST : LinearMap.BilinForm ℂ BRSTSpace := (matterB bForm).tmul ghostB

/-- `ρ 𝐐 = (-1)^{gh} [Λ, 𝐐] ρ` on relative states, for `ρ = ρ_M ⊗ ρ_G`.
Proved: `ghostConjRhoD_proved` (`BRSTConjIdentityProved.lean`). -/
def GhostConjRhoD : Prop :=
  ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    ghConjBRST (brstQ x) = ((-1 : ℂ) ^ g) • brstE n (ghConjBRST x)

/-- `B(E u, v) = i (-1)^{gh u} B(u, E v)` on
relative states, for `B = B_M ⊗ B_G`, `E = [Λ, 𝐐]`.
Proved: `ghostConjBE_proved` (`BRSTConjIdentityBE.lean`). -/
def GhostConjBE : Prop :=
  ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      ghBBRST (brstE n u) v = Complex.I * (-1 : ℂ) ^ g * ghBBRST u (brstE n v)

theorem brstρ_bgGhostData (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    brstρ (bgMatterData hA) bgGhostData = ghConjBRST := rfl

theorem brstB_bgGhostData (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    brstB (bgMatterData hA) bgGhostData = ghBBRST := rfl

/-- **The corrected remainder from the two concrete statements** (`κ = 1`). -/
def bgGhostRemainderI (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hD : GhostConjRhoD) (hE : GhostConjBE) : BGGhostRemainderI hA where
  G := bgGhostData
  hsG := bgGhostData_s
  κ := 1
  hκ := one_ne_zero
  ρ_D := fun n j g x hxr hx => by
    rw [brstρ_bgGhostData, one_mul]
    exact hD n j g x hxr hx
  B_E := fun n j g u hur hu v hv => by
    rw [brstB_bgGhostData]
    exact hE n j g u hur hu v hv

/-- **Affine GU ⇒ Lee–Yang GU with the ghost conjugation constructed.** `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for the canonical pair),
`hD`, `hE` (the two concrete statements above, numerically verified)
and the downstream `symbols`, `character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_ghostConj
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure)
    (hD : GhostConjRhoD) (hE : GhostConjBE)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2
        ((bgGhostRemainderI hA hD hE).pkg hB).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2
        ((bgGhostRemainderI hA hD hE).pkg hB).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd ((bgGhostRemainderI hA hD hE).pkg hB).sp2
        ((bgGhostRemainderI hA hD hE).pkg hB).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgRemainderI hA hB (bgGhostRemainderI hA hD hE) symbols
    character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
