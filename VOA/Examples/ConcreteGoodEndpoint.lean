/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodInterpreted
import VOA.Examples.LeeYangShortcutConcrete

/-!
# The Lee–Yang endpoint with the interpreted Beem–Garner geometry

`leeYang_gradedUnitary_of_affine_concrete'` with its uninterpreted geometry input
`I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n)` replaced by
`interpretedGoodGeometry`: the bigrading is the actual factor `R`-grading (`brstDeg`), the
second differential is derived, and the adjoint relation is proved.

Remaining inputs of `leeYang_gradedUnitary_of_affine_interpreted` (besides the hypothesis `hA`):
`hB` (unitarity of `L_1(sl₂)`), `hG` (ghost-form positivity), `Gh` (the ghost `R`-grading),
`hZ : ZeroModesPreserve Gh`, `hD : RelativeDifferentialGood Gh`,
`hK : InterpretedKahlerAnticomm …`, and the downstream inputs `R` (conjugation data), `symbols`,
`character`, `generators`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`, all stated
for the interpreted geometry.
-/

namespace VOA.ConcreteHodge

open LeeYangTransferAssembly LeeYangShortcut Sl2CosetConcrete Sl2SemiInfinite
open VirGradedUnitarity LeeYang VOA.VertexOperatorAlgebra VOA.GradedUnitaryCohomology

/-- The `ConcreteKahlerGeometry` of the interpreted inputs. -/
noncomputable abbrev interpretedKahler {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)
    (hK : InterpretedKahlerAnticomm Gh hA hB hG hZ hD) : ConcreteKahlerGeometry :=
  concreteKahler (interpretedGoodGeometry Gh hA hB hG hZ hD hK)

/-- **Affine GU ⇒ Lee–Yang GU, with the interpreted Beem–Garner geometry.**
`#print axioms`-clean, conditional on the listed inputs. -/
theorem leeYang_gradedUnitary_of_affine_interpreted
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG)
    (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)
    (hK : InterpretedKahlerAnticomm Gh hA hB hG hZ hD)
    (R : ∀ n hp, GoodComplex.ConjData
      (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD hK) n hp))
    (symbols : LeadingInvariantSymbolDimension (interpretedKahler Gh hA hB hG hZ hD hK))
    (character : LeeYangPBWCharacter)
    (generators : ∀ hp, ClassGeneratorFiltration (interpretedKahler Gh hA hB hG hZ hD hK) hp)
    (vacuumNormalized : HarmonicVacuumNormalized (interpretedKahler Gh hA hB hG hZ hD hK)
      (concreteGUData _ R))
    (creationAdjoint : HarmonicCreationAdjoint (interpretedKahler Gh hA hB hG hZ hD hK)
      (concreteGUData _ R))
    (wordsReal : HarmonicWordsReal (interpretedKahler Gh hA hB hG hZ hD hK)
      (concreteGUData _ R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_concrete' hA hB hG
    (interpretedGoodGeometry Gh hA hB hG hZ hD hK) R symbols character generators
    vacuumNormalized creationAdjoint wordsReal

end VOA.ConcreteHodge
