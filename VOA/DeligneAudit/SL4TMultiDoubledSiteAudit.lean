import VOA.DeligneAudit.SL4TDoubledSiteRankAudit
import VOA.DeligneAudit.SL4TRemainderMinorTransport

/-!
# Full-flag dimensions and transport of remainder strata

The full-flag ring has its literal polynomial presentation: the positive elementary
symmetric functions and a common power cutoff on every root. The finite-generator
identity confirms that only the first B elementary functions are needed.

Proved for all parameters:
* `fullFlag_finite`: finite-dimensionality for every number of roots and cutoff.
* `fullFlag_finrank_le`: dimension at most B! / 2^k when 2k <= B and the cutoff is B-k.
* `alphabetElementary_delete_root` and `twoRoot_complete_vanish`: the deletion and
  complementary-alphabet identities in arbitrary commutative rings.
* `fullFlag_boundary_power_layer`: the root cutoff improvement in every later layer.
* `alphabetRemainderMatrix_coeff` and `finiteAlphabet_remainderMatrix_coeff`: the full
  remainder formula, including powers below the characteristic degree.
* `alphabetRemainder_shift_mem`: the entrywise cutoff shift, obtained by deleting one
  characteristic factor. No deformation or independence theorem is used.
* `remainderTopIdeal_later_layer`: transport of the entire top-minor ideal through the
  later root-power layers, including repeated and zero column indices.

## Not proved here
`FullFlagStratumRankBound` is a defined proposition and is not proved in the files audited
here (it is `fullFlagStratumRankBound` in `SL4TFullFlagStratumRank`). Its statement
uses `FullFlagStratumRing` and `FullFlagStratumConfiguration`, not an abstract replacement
for either ring or count. All these quotient rings are proved finite-dimensional.
The stratum-refined bound needs the dimension induction with the stratum imposed, its
full-alphabet boundary case, and the configuration-count recursion; here only the unrefined
factorial bound is proved.

A direct argument using only top-row minors is not established here either.
Replacing a top row in the determinant argument produces a lower-row minor, and membership
of those minors in the top-row ideal would be needed to remove the deformation argument
from the module bound. No module-dimension conclusion for multiple paired sites is
asserted by this audit.

Implementation conventions:
* The common cutoff N is an independent parameter of `FullFlagRing B N`.
* The first root is peeled. Permuting full-flag positions handles a root outside
  the selected subalphabet in the stratum induction.
* A power layer is presented by the colon ideal `(z^(i+1)) : z^i`.
* Complete functions with negative indices contribute zero through an explicit guard.
* Top minors allow arbitrary column functions; repeated columns have zero determinant.

Axiom check: all main theorems and 87 of the 90 inventoried declarations depend exactly on
`[propext, Classical.choice, Quot.sound]`. The definition `rootPowerLayerIdeal` and its two
membership helpers depend on `[propext, Quot.sound]`.
The following commands inventory every named declaration and audit its dependencies.
-/

-- SL4TFullFlagRing.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_finite
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagRing
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagRoot
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_elementary_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagRoot_pow
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetElementary_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_elementaryPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetComplete_eq_complement
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetComplete_vanish
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetElementary_delete_root
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoRoot_complete
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoRoot_complete_vanish

-- SL4TFullFlagPowerRelations.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.twoRoot_boundary_power_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_boundary_power_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_boundary_power_layer

-- SL4TFullFlagCharacteristic.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_append
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_singleton
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_monic
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_natDegree_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_natDegree
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_characteristicPolynomial
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_delete_expansion
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_deleted_mem

-- SL4TRemainderMatrix.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainderMatrix
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.inverseSeries_trunc_product_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerQuotient
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerQuotient_product
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerQuotient_remainder_degree
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPower_division
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.inverseSeries_trunc_tail_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_coeff_of_large
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainderMatrix_coeff
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.finiteAlphabet_remainderMatrix_coeff

-- SL4TRemainderShift.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_delete_truncated
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainder_shift_of_nilpotent
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetRemainder_shift_mem

-- SL4TFullFlagFinite.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_aeval
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_adjoin_roots
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finite
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_le_ker
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagLift
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagLift_surjective

-- SL4TRootPowerFiltration.lean
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.rootPowerLayerIdeal
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.root_mem_powerLayerIdeal
-- Output: [propext, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.rootPowerLayerIdeal_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.rootPowerLayer_finrank
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.rootPowerFiltration_finrank

-- SL4TFullFlagPowerLayers.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagPowerLayer
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayerRoot
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_first_zero
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_elementary
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayerRoot_pow
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_aeval_surjective
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_rank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetRoot_powerLayer_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayerRoot_lower_pow
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagPowerLayer_lower_rank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_recursion

-- SL4TFullFlagRank.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_empty_rank_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_mul_pow_two_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_le

-- SL4TRemainderStrata.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_map
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_cutoff_mono
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_of_small
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_eq_top
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagStratumRing
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finite
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagConfiguration
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagStratumConfiguration
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.FullFlagStratumRankBound

-- SL4TRemainderMinorTransport.lean
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.determinant_updateColumn_mem_of_span
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_shift_of_nilpotent
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_shift_mem
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_shift_le
-- Output: [propext, Classical.choice, Quot.sound]
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_later_layer
