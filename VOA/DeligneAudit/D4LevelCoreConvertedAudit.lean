import VOA.DeligneAudit.D4LevelCoreGenerationAudit
import VOA.DeligneAudit.D4LevelReductionCoreComplete

/-!
The complete converted ideal and the cyclic universal core presentation for every bottom triple.

The complement map sends a complete core coefficient to a signed elementary function of the
original central alphabet. Exact middle raising selects distinct central slots, retaining all
positional multiplicities. Multiplying the elementary product by the complete series of the
selected slots cancels those slots. The residual polynomial has degree at most the number of
unselected central slots. Its higher coefficients vanish identically, even after multiplication
by arbitrary coefficient and raising-mode polynomials.

`coreRaisingSourceEvaluation_complete_mul_zero` proves this vanishing in every saturated source
module before taking a level quotient. `coreGrassmannianEvaluation_converted` descends the entire
ideal to the level coinvariant. Thus no additional inclusion of a fine-key prefix in the next
level is needed: the Grassmannian descent and complement identification already proved for the
bottom evaluation are sufficient.

`universalCorePresentation` discharges the last presentation hypothesis for all nonnegative
triples. `levelTruncationBound_of_truncatedCoreRank` has only the core rank estimate as a
mathematical hypothesis. `levelTruncationBound_singleAdjoint_interior` gives the family
at grade `κ` and level `κ + 2`, with central count `m - κ - 1` positive.

Not proved here: `TruncatedCoreRankBound 1 κ c` for all `κ` and `c ≥ 1`.
The cell filtration and its per-cell rank estimates are not asserted here. The general core
rank bound for larger adjoint count is also open. No unconditional interior level bound
or global fusion bound is claimed by this module.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingChoices_injective
#print axioms VOA.DeligneAudit.D4LevelReduction.centralRaisingIteratedEvaluation_choices
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_choices
#print axioms VOA.DeligneAudit.D4LevelReduction.selectedAlphabet_complete_cancellation
#print axioms VOA.DeligneAudit.D4LevelReduction.centralElementaryProduct_map
#print axioms VOA.DeligneAudit.D4LevelReduction.coreBottomModePolynomial_complete
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_hsymm
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_complete_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_complete_mul_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingCurrent_commute
#print axioms VOA.DeligneAudit.D4LevelReduction.leviMiddleRaising_operator
#print axioms VOA.DeligneAudit.D4LevelReduction.middleRaisingProduct_reverse
#print axioms VOA.DeligneAudit.D4LevelReduction.middlePositionProduct_ambient
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSourceEvaluation_choices
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSourceEvaluation_complete_mul_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingLevelLift_coe
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_representative
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingEvaluation_zero_of_source
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingCompleteRepresentative_map
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_complete_mul_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianEvaluation_converted
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_converted
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCorePresentation
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_truncatedCoreRank
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_singleAdjoint
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_singleAdjoint_interior
