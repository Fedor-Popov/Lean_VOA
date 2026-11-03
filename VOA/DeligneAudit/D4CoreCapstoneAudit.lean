import VOA.DeligneAudit.D4CoreConditionalCapstoneAudit
import VOA.DeligneAudit.D4LevelReductionCoreCapstone

/-!
The D4 capstone requires only the interior truncated core rank bounds.

The Demazure letter-count layers map onto the intrinsic eigenspaces of the node-one
fundamental coweight. Each eigenspace satisfies its own right-exact level rank bound.
These eigenspaces are an internal direct sum, supported on the interval from minus
the multiplicity to the multiplicity.

Grade symmetry is proved on the actual truncated module. The diagonal sl2 of the
orthogonal roots alpha-one and the highest root has Cartan element twice the
fundamental coweight. The finite grade support proves nilpotence of its raising and
lowering operators. The three finite root exponentials give an invertible operator
reversing that Cartan element. Thus opposite grades have equal dimensions. This
shorter reflection route proves precisely the grade symmetry required by the reduction.
It makes no assertion that the individual opposite-grade level pieces are comparable.

The nonnegative-level coverage, the grade rank estimate, and the
symmetric four-colour count give `univTruncatedRank_of_coreBounds` and
`fusionTotalDim_of_coreBounds`. The proved character realization then gives
`d4_classicallyFree_of_coreBounds`, with exactly the conclusion of the capstone.
Its only hypothesis is the family of interior truncated core rank bounds.

Axiom check: every audited declaration depends exactly on `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry` and no project axiom is used.

Not proved here: the interior family `TruncatedCoreRankBound` is the explicit hypothesis; its
cell filtration and the single-adjoint core bounds are not treated in this module. A piecewise
negative-grade transfer is neither proved nor used by this capstone.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeImage_eq_eigenspace
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_rank_le_levelSum
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_interval_isInternal
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_finrank_neg
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_eq_bot_of_outside_interval
#print axioms VOA.DeligneAudit.D4LevelReduction.gradeTarget_nonnegative_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.univTruncatedRank_of_coreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.fusionTotalDim_of_coreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_coreBounds
