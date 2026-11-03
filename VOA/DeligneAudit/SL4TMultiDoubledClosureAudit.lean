import VOA.DeligneAudit.SL4TMultiDoubledFinalAudit
import VOA.DeligneAudit.SL4TMiddleFlagInvariantQuotient

/-!
# Colour-power contraction and the actual middle-flag tail quotient

The coordinate-power ideal contracts to exactly the ideal of colour-block power sums
in every mode above the cutoff. The proof works for arbitrary finite position sets
and arbitrary colours. Its marked-exponent induction decreases the number of occupied
variables: the unused positions give equal averaged monomials, and the occupied positions
produce smaller supports. A nonzero natural scalar is inverted over the complex numbers.
`colourCoordinateIdeal_contract` also includes zero cutoff and the empty alphabet.

`colourStratumIdeal_contract` adds the actual elementary and top-minor generators.
`colourTailStratum_finrank` gives the exact refined orbit count in that explicit
presentation. `ColourFlagRing` then imposes the elementary relations first;
`colourFlagStratumInvariantEquiv` is the algebraic Reynolds descent with the tail and
minor ideals specified by their generators. `colourFlagTailStratum_finrank` gives its
exact refined dimension. These results hold for every admissible pair of site counts
and every threshold, including empty strata and the empty-minor boundary.

The blockwise fundamental theorem is reindexed onto the actual Young subgroup.
`colourElementaryPresentation` gives elementary coordinates for its fixed algebra, and
`colourElementaryPresentation_powerSum` identifies the actual block power sums in those
coordinates. There is no additional symmetric-polynomial presentation hypothesis.

`middleFlagInvariantEvaluation` specializes these coordinates to the mixed ring.
It is surjective for every valid zero-outer-label tuple. Positive block power sums map to
`middleFlagTailSymbols`; the contracted coordinate-power ideal maps exactly onto
`middleFlagAllTailIdeal`, by
`middleFlagInvariantEvaluation_contractedCoordinateIdeal`.
`middleFlagPosition_contractedCoordinateIdeal` supplies the canonical colouring and the
required fibre equivalences for every valid tuple, with no additional existence premise.
The positive elementary relations vanish, so the specialization descends to the partial
flag ring and then to a surjection `middleFlagTailQuotientEvaluation` onto the actual
all-tail coefficient quotient.

## Proved and not proved here
* The generator contraction and its specialization to the actual all-tail ideal are proved.
* The partial-flag and actual mixed quotients are connected by a proved surjection.
  Injectivity is *not* proved; exact source dimensions must not be asserted for the target.
  A source flag can be transported by the surjection.
* Not proved: the transport of the top-minor strata and the characteristic polynomial
  through that surjection, together with the strictly increasing degree correction.
* Not proved: a multiplicity-preserving correspondence between the attained colour
  configurations and `multiDoubledSiteCellCatalog`, respecting the selected-double statistic.
* `MultiDoubledSiteCoefficientFlag` is not constructed here.
  `truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags` remains conditional;
  `truncatedWeyl_sl4_multiDoubledSite_rank_le` is not proved here.

The commands below inventory every explicit declaration of this layer, including
definitions and the local finite-type instance, by file.
-/

-- SL4TColourPowerSumContraction.lean
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverageToFixed_action
#print axioms VOA.DeligneAudit.SL4T.colourPermutationFintype
#print axioms VOA.DeligneAudit.SL4T.ColourPolynomialRing
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialPowerSum
#print axioms VOA.DeligneAudit.SL4T.colourPowerSumTailIdeal
#print axioms VOA.DeligneAudit.SL4T.colourPositionSwap
#print axioms VOA.DeligneAudit.SL4T.monomial_rename_swap_of_zero
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_move_power
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_powerSum_mul
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_monomial_mem_tail
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialAverage_mem_tail
#print axioms VOA.DeligneAudit.SL4T.colourPolynomialPowerSum_mem_coordinateIdeal
#print axioms VOA.DeligneAudit.SL4T.colourCoordinateIdeal_contract_of_pos
#print axioms VOA.DeligneAudit.SL4T.colourPowerSumTailIdeal_zero
#print axioms VOA.DeligneAudit.SL4T.colourCoordinateIdeal_contract
#print axioms VOA.DeligneAudit.SL4T.colourCoordinateIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.colourCoordinateIdeal_contract_sup

-- SL4TColourStratumPresentation.lean
#print axioms VOA.DeligneAudit.SL4T.colourFullElementary
#print axioms VOA.DeligneAudit.SL4T.colourSymmetricIdeal
#print axioms VOA.DeligneAudit.SL4T.colourSymmetricIdeal_map
#print axioms VOA.DeligneAudit.SL4T.colourRemainderTopMinor_fixed
#print axioms VOA.DeligneAudit.SL4T.colourRemainderTopMinor
#print axioms VOA.DeligneAudit.SL4T.colourRemainderTopIdeal
#print axioms VOA.DeligneAudit.SL4T.colourRemainderTopIdeal_map
#print axioms VOA.DeligneAudit.SL4T.colourFullFlagIdeal_contract
#print axioms VOA.DeligneAudit.SL4T.colourStratumIdeal_contract
#print axioms VOA.DeligneAudit.SL4T.ColourTailStratumRing
#print axioms VOA.DeligneAudit.SL4T.colourTailStratum_finrank

-- SL4TColourFlagTailQuotient.lean
#print axioms VOA.DeligneAudit.SL4T.ColourFlagRing
#print axioms VOA.DeligneAudit.SL4T.colourFlagPowerSum
#print axioms VOA.DeligneAudit.SL4T.colourFlagTailIdeal
#print axioms VOA.DeligneAudit.SL4T.colourFlagTailIdeal_eq_span
#print axioms VOA.DeligneAudit.SL4T.colourFlagTopIdeal
#print axioms VOA.DeligneAudit.SL4T.colourFlagStratumQuotientEquiv
#print axioms VOA.DeligneAudit.SL4T.colourFlagTailStratum_finrank
#print axioms VOA.DeligneAudit.SL4T.colourFlagStratumInvariantEquiv

-- SL4TColourElementaryPresentation.lean
#print axioms VOA.DeligneAudit.SL4T.permutationFixedAlgebraEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockSlotEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockRelabelingEquiv
#print axioms VOA.DeligneAudit.SL4T.colourBlockSlotEquiv_action
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_apply

-- SL4TColourElementaryCoordinates.lean
#print axioms VOA.DeligneAudit.SL4T.blockElementary_profile_generator
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_generator
#print axioms VOA.DeligneAudit.SL4T.colourElementaryCoordinate
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_coordinate
#print axioms VOA.DeligneAudit.SL4T.colourPowerSumCoordinate
#print axioms VOA.DeligneAudit.SL4T.colourElementaryPresentation_powerSum

-- SL4TMiddleFlagInvariantEvaluation.lean
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoordinateEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoordinateEvaluation_elementary
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoordinateEvaluation_powerSum
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_powerSum
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_eq_span
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_tailIdeal
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_contractedCoordinateIdeal

-- SL4TMiddleFlagInvariantSurjection.lean
#print axioms VOA.DeligneAudit.SL4T.middleFlag_secondAmbient_elementary
#print axioms VOA.DeligneAudit.SL4T.middleFlagElementary_generates
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoordinateEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionEquiv
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionColour
#print axioms VOA.DeligneAudit.SL4T.middleFlagPositionFibre
#print axioms VOA.DeligneAudit.SL4T.middleFlagPosition_contractedCoordinateIdeal

-- SL4TMiddleFlagInvariantQuotient.lean
#print axioms VOA.DeligneAudit.SL4T.colourFullElementary_newton
#print axioms VOA.DeligneAudit.SL4T.middleFlagInvariantEvaluation_elementary_zero
#print axioms VOA.DeligneAudit.SL4T.colourSymmetricIdeal_le_middleFlagKernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.middleFlagPartialInvariantEvaluation_tailIdeal
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailQuotientEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailQuotientEvaluation_surjective
