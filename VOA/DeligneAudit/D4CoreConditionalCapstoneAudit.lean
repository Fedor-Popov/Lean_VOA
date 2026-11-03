import VOA.DeligneAudit.D4LevelCoreConvertedAudit
import VOA.DeligneAudit.D4CharRound109Audit
import VOA.DeligneAudit.DeligneSeries
import VOA.DeligneAudit.D4LevelReductionConditionalCapstone

/-!
The D4 capstone has an additional negative-grade transfer obligation.

`levelTruncationBound_of_nonnegative_coreBounds` exhaustively treats every integer level at
every nonnegative grade. The excluded, odd, negative-adjoint, and negative-central cases use
the established empty-level bound. The remaining indices have a natural bottom triple;
zero adjoint count and zero central count use the established boundary theorems, and the
interior uses the supplied core rank bound. This argument includes multiplicity zero.

The grade itself is an integer. Its negative values are not excluded by `levelIndices` or
the empty-level criteria. For every positive multiplicity, `negativeExtremalLevel_mem`,
`negativeExtremalLevel_not_empty`, and `negativeExtremalLevel_no_bottomTriple` certify that
the grade-level pair `(-m,m)` survives all those criteria but cannot have a natural middle
label. These certificates concern index support; they do not assert a dimension of the
corresponding universal piece.

`levelTarget_neg_grade` proves the combinatorial reflection symmetry for all multiplicities
and integer indices. The missing representation-theoretic statement is named
`NegativeGradeRankTransfer`: the actual universal level coinvariant at negative grade has
dimension at most the coinvariant at the opposite grade and the same level. It does not
follow from the level or Levi interfaces of this library, and it is not asserted here.

`d4_classicallyFree_of_coreBounds_and_negativeGradeTransfer` has exactly the conclusion of
the D4 capstone, using the proved character realization. Its two hypotheses are
explicit: the interior core bounds and the additional grade transfer. It is not the
capstone from core bounds alone; that theorem is not proved here in the negative-grade case.
The single-adjoint core cell filtration is not treated in this module.

Axiom check: the five main theorems depend exactly on `[propext, Classical.choice, Quot.sound]`
and no `sorryAx` occurs; the arithmetic index helpers use only a subset of those axioms.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_nonnegative_coreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_neg_grade
#print axioms
  VOA.DeligneAudit.D4LevelReduction.levelTruncationBound_of_coreBounds_and_negativeGradeTransfer
#print axioms
  VOA.DeligneAudit.D4LevelReduction.fusionTotalDim_of_coreBounds_and_negativeGradeTransfer
#print axioms
  VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_coreBounds_and_negativeGradeTransfer
