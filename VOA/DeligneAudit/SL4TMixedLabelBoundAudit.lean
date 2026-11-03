import VOA.DeligneAudit.SL4TMixedSiteRingAudit
import VOA.DeligneAudit.SL4TTruncationCutoff
import VOA.DeligneAudit.SL4TRadicalGrassmannianPresentation

/-!
The mixed-label truncated current-module presentation and its first Levi multiplicities.

The universal target is `MixedLabelTruncatedRank`. Its equivalence to the cyclic-module
statement with the single cutoff mode is proved. Universal finiteness follows from the
local Weyl theorem; the rank bound proved here is `4^a * 6^b * 4^a`.

The merged radical multiplicity spaces retain all mode degrees. Their highest-weight,
sharp lowering, finiteness, and Cartan power-sum identities are proved for all labels.
The tensor product of three Grassmannian rings and its binomial upper bound are constructed.

**Not proved here:** `RadicalGrassmannianPresentation`, a proposition defining an
equivariant surjection onto the actual multiplicity space. For supported counts, its word
evaluator, the Grassmannian relations lying in its kernel, and surjectivity are open, as is
the vanishing of unsupported count multiplicities. The second Levi multiplicity
presentation and the assembly of the bound `15^a * 6^b` are not proved here.

The declarations below form the complete inventory of this layer.
Axiom check: every theorem uses exactly `[propext, Classical.choice, Quot.sound]`.
-/

-- SL4TMixedLabelModule.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeylSpec
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeylSpec_sat_iff
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.current_truncation_on_cyclic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.presentedCurrent_cyclic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.MixedLabelModule
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.MixedLabelTruncatedRank
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelModule_finite_and_local_bound

-- SL4TMixedLabelUniversal.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.presentedCurrent_map_range
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.presentedCurrent_cyclic_rank_le
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank_iff_cyclic

-- SL4TTruncationCutoff.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.current_cutoff_of_single_mode
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.truncatedWeylSpec_sat_iff_cutoff
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.mixedLabelTruncatedRank_iff_generator_cutoff

-- SL4TRadicalCountLayers.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer
-- Axioms: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCounts
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuotCurrent
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_le_cyclic
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_finite
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_cartan_positive
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_cartan_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_raising
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_raising
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_cartan_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_cartan_positive
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_lowering_nilpotent
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_lowering_sharp

-- SL4TRadicalPowerSums.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_comm
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_source_zero
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalPowerSumWord
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_word
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.leviCartan_eq_alphabet_difference
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.leviCartan_word_powerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_extra_cartan_positive
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_alphabet_current

-- SL4TRadicalMultiplicityAction.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_extra_cartan
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_alphabet_current
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_mk
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_alphabet_current
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_word

-- SL4TRadicalGrassmannianPresentation.lean
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalGrassmannianRing
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.grassmannianPowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianPowerSum
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianRing_finite_rank_le
-- Axioms: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.RadicalGrassmannianPresentation
