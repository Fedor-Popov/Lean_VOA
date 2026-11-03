import VOA.Examples.LeeYangShortcutAssembly
import VOA.Examples.ConcreteHodgeAssembly

/-!
# The Virasoro-image shortcut with the concrete Beem--Garner discharge

`leeYang_gradedUnitary_of_affine'` with its `kahler`, `weakGU` and `gu` fields
supplied by `ConcreteHodge` (`concreteKahler`, `concreteKahler_weakGU`,
`concreteGUData`). No coset identification is used.
-/

namespace VOA.LeeYangShortcut

open LeeYangTransferAssembly ConcreteHodge Sl2CosetConcrete
open VirGradedUnitarity LeeYang Sl2SemiInfinite VOA.VertexOperatorAlgebra

/-- **Affine GU ⇒ Lee--Yang GU, concrete form, no coset identification.**
`#print axioms`-clean, conditional on: `hB` (unitarity of `L_1(sl2)`), `hG`
(ghost-form positivity), `I` (Beem--Garner Lemma 3.16 geometry), `R`
(conjugation data), `symbols`, `character`, the filtration generator tests,
and the three harmonic-metric bridges. -/
theorem leeYang_gradedUnitary_of_affine_concrete'
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤)
    (I : ∀ n, ConcreteGoodGeometry n (assemblyForm BB RB PG n))
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood I n hp))
    (symbols : LeadingInvariantSymbolDimension (concreteKahler I))
    (character : LeeYangPBWCharacter)
    (generators : ∀ hp, ClassGeneratorFiltration (concreteKahler I) hp)
    (vacuumNormalized : HarmonicVacuumNormalized (concreteKahler I) (concreteGUData I R))
    (creationAdjoint : HarmonicCreationAdjoint (concreteKahler I) (concreteGUData I R))
    (wordsReal : HarmonicWordsReal (concreteKahler I) (concreteGUData I R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine' hA
    { kahler := concreteKahler I
      weakGU := concreteKahler_weakGU hB hG I
      gu := concreteGUData I R
      symbols := symbols
      character := character
      generators := generators
      vacuumNormalized := vacuumNormalized
      creationAdjoint := creationAdjoint
      wordsReal := wordsReal }

end VOA.LeeYangShortcut
