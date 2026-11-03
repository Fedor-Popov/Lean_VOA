import VOA.DeligneAudit.D4CoreSingleAdjointAudit
import VOA.DeligneAudit.D4LevelReductionCoreSubsetCellBound

/-!
Current truncation at the union size of every honest-pair core cell.

The main result is `D4LevelReduction.coreCellTruncation`. For every nonnegative triple
`a, b, c`, every finite-dimensional current module `Q`, every coefficient map `π` satisfying
`CoreRelations Q a b c π`, and every `CoreCellFlag a b c`, it proves the proposition
`CoreCellTruncation a b c Q π F`, assuming only that currents of modes at least `a+b+c`
vanish on the module. Neither a new coefficient action nor a cyclicity hypothesis is needed.
The zero-cutoff case is included. `coreCellPiece_current_tail` gives the resulting tail
annihilation on the whole cyclic cell piece, without a residual truncation hypothesis.

The representation-theoretic argument uses the highest root to avoid five separate
characteristic calculations. `coreHighest_currentRelations` supplies its rank-one current
triple. `coreLowering_locally_nilpotent` uses finiteness of the Cartan spectrum, and
`coreHighest_lowering_nilpotent` sharpens the lowering exponent at a highest vector.
The two positive Cartan alphabets add at the highest root; `coreUnion_newtonCoeff` identifies
their Newton coefficients with the product series. Corrected Garland therefore proves
`coreHighest_characteristic`, with polynomial equal to the product of the two Grassmannian
characteristics. The cell characteristic relation gives
`coreCellGenerator_highest_truncation`. Positive zero-mode commutators then give all six
negative roots in `coreCellGenerator_negative_truncation`, including the middle lowering root.

For the middle raising root a sharper argument suffices. On each cell quotient the first
outer root has highest weight `a` and zero positive Cartan modes. Ordinary Garland gives its
lowering cutoff at `a`. The bracket of the first composite positive root with that outer
lowering root is minus the middle raising root. Consequently
`coreCellGenerator_middle_raising_truncation` holds at every mode at least `a`.
Since the cell union contains the adjoint alphabet, this implies the required union cutoff.
This proof does not require a separate one-letter function model or converted-ideal argument.

There is also a precise conditional bridge. For a single adjoint site,
`coreCell_singleAdjoint_localWeyl` proves the local Weyl relations from just the additional
condition that the middle raising zero mode of the cell generator belongs to the preceding
module term. If the adjoint site lies among the complement sites,
`coreCellCutoff_of_subset` identifies the cutoff with `1+b`, and
`coreCell_subset_rank_of_middle_zero` applies the proved mixed-label rank bound to obtain
`finrank(coreCellPiece) ≤ 15 * 6^b`.

**Not proved here:** the `hzero` hypothesis of `coreCell_subset_rank_of_middle_zero`
is not discharged. It is the statement
`Q.op 3 0 (π (F.generator i)) ∈ coreCellFiltration 1 b c Q π F i`
for cells whose adjoint singleton is contained in the complement subset. Positive middle
raising modes are already proved to lie in the preceding term. The missing zero-mode
annihilation remains to be derived from the converted complete-function relations and the
coefficient cell structure. No subset-cell annihilation is silently built into `CoreCellFlag`.
The non-subset cell rank estimate, the final cell count, and
`TruncatedCoreRankBound 1 b c` are not proved here.

Axiom check: every main theorem is audited below; all audit outputs are exactly
`[propext, Classical.choice, Quot.sound]`, and no `sorryAx` occurs.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.coreLowering_locally_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_lowering_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCurrent_commutator
#print axioms VOA.DeligneAudit.D4LevelReduction.coreOuter_currentRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_currentRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannian_newtonSeries
#print axioms VOA.DeligneAudit.D4LevelReduction.coreUnion_newtonCoeff
#print axioms VOA.DeligneAudit.D4LevelReduction.coreUnion_descendingPolynomial
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighestCartan_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighestCartan_powerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_characteristic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_highest_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_lowering_modes
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellCutoff_bounds
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCurrent_mem_of_bracket
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_outer_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_middle_raising_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_negative_truncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellTruncation
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellPiece_current_tail
#print axioms VOA.DeligneAudit.D4LevelReduction.coreFinite_simple_lowering
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellCutoff_of_subset
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_singleAdjoint_localWeyl
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_subset_rank_of_middle_zero
