import VOA.DeligneAudit.D4LevelCoreModuleAudit
import VOA.DeligneAudit.D4LevelReductionPresentationResidual

/-!
Audit of the honest Grassmannian presentation of the universal bottom Cartan orbit.

For all nonnegative labels, `universalCoreEvaluation` is a linear map from `CoreBaseRing`
to `UniversalCorePiece`. It sends the unit to `universalCoreBottom`, has exactly the image
of `universalBottomCartanMap`, and satisfies `CoreCartanAction`. The complement alphabet
is identified by `coreGrassmannianToBottom_leftElementary` and
`coreGrassmannianToBottom_leftComplete`; its positive power sums are the negatives of
the central-letter power sums. Both full Grassmannian ideals vanish under actual mode
evaluation. The construction uses the complete-function relations and the
ideal property of symmetric level relations, without assuming a presentation.

The converted ideal condition is proved at raising length zero and at every length
greater than the central count. The former ideal is zero; in the latter case the entire
raising evaluator is zero before imposing the converted ideal.

Two precise residuals remain:
* For `1 ≤ j ≤ c`, containment of `coreRaisingIdeal a b c j` in the kernel of
  `coreRaisingEvaluation (universalCoreCurrent a b c) a b c (universalCoreEvaluation a b c) j`.
* `cycSubG (universalCoreCurrent a b c) (universalCoreBottom a b c) = ⊤`.

The first needs the arbitrary-mode middle-root conversion identity for complete
functions in the complement and raising alphabets, including ideal multiples. A bound
on the number of raising letters supplies only the overfull case. The second concerns
the entire Levi level piece; generation of its bottom Cartan image does not prove it.
`levelTruncationBound_of_coreRank_raisingWindow_cyclic` remains conditional on both
residuals as well as `TruncatedCoreRankBound`. No unconditional core presentation or
level bound from the core rank bound alone is asserted.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.complementAlphabet_involutive
#print axioms VOA.DeligneAudit.D4LevelReduction.grassmannianComplement_powerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomCentral_grassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.bottomAdjoint_grassIdeal
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_leftElementary
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_leftComplete
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianToBottom_complementPowerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_one
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_range_eq
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_parabolic
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_raising_overfull
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingIdeal_zeroLength
#print axioms VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation_converted_of_window
#print axioms
  VOA.DeligneAudit.D4LevelReduction.universalCorePresentation_of_raisingWindow_and_cyclic
#print axioms
  VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_coreRank_raisingWindow_cyclic

#check VOA.DeligneAudit.D4LevelReduction.universalCoreEvaluation
#check VOA.DeligneAudit.D4LevelReduction.UniversalCorePresentation
#check VOA.DeligneAudit.D4LevelReduction.TruncatedCoreRankBound
