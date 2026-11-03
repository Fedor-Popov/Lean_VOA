import VOA.DeligneAudit.D4LevelBoundsAdjointAudit
import VOA.DeligneAudit.SL4TDoubledSiteRankAudit
import VOA.DeligneAudit.D4LevelReductionBottomPowerSums

/-!
The bottom Cartan space and its relations in the D4 level coinvariant.

All declarations are in the D4LevelReduction namespace.

Proved mathematical content:

* The exact-level multiplicity span is the sum of the existing radical key layers
  at fixed grade and level, over every current degree. It uses keyLayer rather
  than keyOrbit: Cartan currents preserve this space, while outer raising currents
  increase the level. This reuses the existing filtration without changing it.
* The five positive parabolic currents send the exact-level multiplicity span to
  the next level. This holds for all multiplicities and all integer grades and
  levels. On the actual universal coinvariant they therefore annihilate the whole
  Cartan orbit of the zero-mode bottom vector for every natural triple of labels.
* The bottom Cartan orbit has the expected equal outer labels and middle label.
  Positive Cartan modes act on bottom words by the two alphabet power-sum shifts.
  The extra reductive Cartan acts by the negative adjoint-alphabet power sum.
* The adjoint complete-symmetric tail vanishes in the source module. The central
  complete-symmetric tail vanishes modulo the next level by highest-Levi-root
  conversion. Every incomplete contraction has strictly larger level. Arbitrary
  Levi words preserve this relation. Symmetric mode multiplication preserves level
  relations, so their kernel is an ideal in the colour power-sum algebra.
* The actual universal level coinvariant is finite and its high semisimple Levi
  currents vanish as operators. The core rank assertion is stated with the honest
  two-Grassmannian ring, the three Cartan symbols, and the full converted ideal.
  The threshold uses c < j + n, so overfull raising words impose the constant
  relation; natural-number subtraction does not discard that case.

Not proved here:

`UniversalCorePresentation a b c` is a *definition* of an outstanding proposition.
No theorem establishes it in these files. Its missing construction is a linear
map from CoreBaseRing a b c into UniversalCorePiece a b c, taking one to the
bottom vector, with image in the actual bottom Cartan orbit, together with:

* CoreCartanAction: descent through both Grassmannian ideals and the complement
  alphabet identification, with the positive-mode Cartan intertwining formulas;
* CoreConvertedRelations: the complete-function ideal of the union of the
  complement and raising alphabets lies in every raising evaluator's kernel;
* cyclic generation of the entire universal level piece by the bottom vector.

The two complete-symmetric source-vector relations do not by themselves provide
that map. Applying Levi words to the central relation is also not identified here
with the full converted polynomial ideal. In particular, the higher-key
relations cannot simply be substituted for higher-level relations.

TruncatedCoreRankBound a b c is a separate outstanding core estimate. It says
that every finite cyclic semisimple Levi current module, truncated at a+b+c, with
CoreRelations has dimension at most levelTarget (a+b+c) b (2*a+b).
The theorem levelTruncationBound_of_corePresentation is explicitly conditional on
both TruncatedCoreRankBound and UniversalCorePresentation. The full universal
presentation reduction and the interior level bounds are not claimed proved.

A route to the presentation: build the separately symmetric bottom evaluator; use the
proved complete tails and ideal closure to descend it to the two Grassmannian
factors, then identify the complement alphabet. The converted polynomial
ideal relation and bottom cyclic generation are needed before applying the core estimate.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.raisingReplacement_grade_level
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_simple_raise
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_parabolic_raise
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.levelMultiplicitySpan_extraCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_levi_invariant
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantRelations_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantCurrent
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_le_multiplicity
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartan_parabolic_annihilation
#print axioms VOA.DeligneAudit.D4LevelReduction.universalBottomCartan_parabolic_annihilation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomConversionTerm_mem_next
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_completeRelation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_completeRelation
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_completeRelation_leviWord
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomMultiplicitySpan_cartan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanSpan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.levelModeRelation_mul
#print axioms VOA.DeligneAudit.D4LevelReduction.levelModeRelationIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomWord_cartanPowerSums
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomWord_extraCartanPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingIdeal_eq_top_of_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_zero_of_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.levelCoinvariantCurrent_high
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCartanToLevel_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCorePiece_finite
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreRelations_of_bottomImage
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_corePresentation

#check VOA.DeligneAudit.D4LevelReduction.UniversalCorePresentation
#check VOA.DeligneAudit.D4LevelReduction.TruncatedCoreRankBound
