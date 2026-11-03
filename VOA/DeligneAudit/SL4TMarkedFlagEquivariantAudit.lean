import VOA.DeligneAudit.SL4TMarkedFlagDeformationAudit
import VOA.DeligneAudit.SL4TMarkedFlagEquivariantStrata

/-!
# The deformation and the equivariant point algebras of the marked full-flag strata: audit

**Status.** For the marked full flags with one double (`k = 1`) the stratum quotients are
identified, for all parameters, with the graded point algebras of the configurations with fewer
selected doubles, equivariantly for every finite group of position permutations preserving the
marked group `V` and the selected set `Y`. Notation: `Z = Yᶜ`, and `c(Z)` is the subleading
coefficient of `∏_Z (1 - x t)`.

* **Counts** (`SL4TMarkedFlagConfigurationCount`).
  `2 · #{double ⊄ Y} + 2 C(|Y|,2) (n-2)! = n!` (`oneDoubleStratum_card`); the configurations
  with fewer than `j` selected doubles plus the lower-bound counts give all configurations
  (`singlyMarked_oneDouble_count`,
  `doublyMarked_oneDouble_count`, `doublyMarked_twoDouble_count`).
* **Deformation, step 3b** (`SL4TMarkedFlagStratumDeformation`). The top-row `j`-minors of the
  columns `t^(h+1+c)` modulo `P_Y` are leading relations of the configurations with fewer than
  `j` selected doubles, for every `j` (`singlyMarked_remainderTopIdeal_le`,
  `doublyMarked_remainderTopIdeal_le`); so is `∏ (V ∩ Y)` times every top-row minor of the
  columns `t^(h+c)` (`singlyMarked_markedRemainderMinor_mem`).
* **Exactness** (`SL4TMarkedFlagStratumExactness`). The polynomial stratum ideals
  `flag + (∏ Z, ∏ (V ∩ Y) c(Z))` (singly marked, `j = 1`), `flag + (∏ Z, c(Z))` and
  `flag + ((∏ Z)²)` (doubly marked, `j = 1, 2`) **equal** the leading-relation ideals of those
  configurations (`singlyMarkedSelectedStratumIdeal_eq`,
  `doublyMarkedOneSelectedStratumIdeal_eq`, `doublyMarkedTwoSelectedStratumIdeal_eq`).
  Hypotheses: `m ≥ 1`, `Y ≠ ∅`, `Z ≠ ∅`, `V ≠ ∅` (and `U ≠ ∅` doubly marked; `|Y| ≥ 2` for
  `j = 2`).
* **Joint top-row ideals** (`SL4TMarkedFlagJointStratumCount`). For the actual joint ideal
  `G_j` of `(t^(h+1), s t^h)` over the flag ring: `dim C/G_1 = #X_{<1}` (singly marked,
  `s = ∏ (V ∩ Y)`), `dim C/G_j = #X_{<j}`, `j = 1, 2` (doubly marked, `s = 0`).
* **Equivariance** (`SL4TMarkedFlagEquivariantStrata`). Position permutations preserving `V`
  and `Y` relabel the marked configurations (`singlyMarkedRelabel`, `doublyMarkedRelabel`); for
  every finite group of such permutations the invariants of the stratum quotient have dimension
  the number of orbits of configurations with fewer than `j` selected doubles
  (`singlyMarkedSelectedStratum_invariant_finrank`,
  `doublyMarkedOneSelectedStratum_invariant_finrank`,
  `doublyMarkedTwoSelectedStratum_invariant_finrank`).

**Not proved here.** `OneAdjointStratumCount B 1`. Its parts for `k = 1`:

* proved: conjunct 3, the joint-ideal equation (`adjointSiteJointTopIdeal_eq_sup`);
* proved: the flag level `C/G_j ≅ gr C[X_{<j}]`, equivariantly, for generic `Y`
  (`SL4TMarkedFlagEquivariantStrata`);
* open: the edge cases `Y = ∅`, `Z = ∅`, `|Y| < 2` (`j = 2`), `V = ∅` or `U = ∅`;
* proved: the unmarked blocks `(d₁, d₃) = (0, 1)`
  (`fullFlagStratum_finrank_eq_configurations`, `colourStratum_invariant_finrank`);
* open: the descent to `AdjointSiteCoefficientRing`, namely
  - a surjection (colour-invariant flag ring) ↠ `MixedRing q ⧸ adjointSiteKernelIdeal q (B-1)`
    (only a surjection is needed for the upper bound),
  - `(G_j)^H ↦ adjointSiteJointTopIdeal` (minors in `e(Y)`, `h(Y)`, `s`),
  - `#orbits(X_{<j}) = adjointSiteWordCount B 1 q 0 - adjointSiteWordCount B 1 q j`.

For `j` above the number of T-points (`j ≥ 2` singly marked, `j ≥ 3` doubly marked, `j ≥ 2`
unmarked) no site word has `j` T-states, so `w_j = 0` and conjunct 2 follows from conjunct 1
(`A/G_j` is a quotient of `A`); `G_j = 0` is not needed for the upper bound.
-/

-- SL4TMarkedFlagConfigurationCount.lean
#print axioms VOA.DeligneAudit.SL4T.two_mul_choose_two_mul_factorial
#print axioms VOA.DeligneAudit.SL4T.fullFlagDoublesIn_univ_one
#print axioms VOA.DeligneAudit.SL4T.finset_eq_map_succ_of_zero_notMem
#print axioms VOA.DeligneAudit.SL4T.oneDoubleStratum_card
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles_card
#print axioms VOA.DeligneAudit.SL4T.sum_deletedGroup_choose_two
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_oneDouble_count
#print axioms VOA.DeligneAudit.SL4T.subtypeSigmaEquivSigmaSubtype
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles_card
#print axioms VOA.DeligneAudit.SL4T.sum_ite_mem_eq
#print axioms VOA.DeligneAudit.SL4T.pair_sum_selected
#print axioms VOA.DeligneAudit.SL4T.nested_pair_sum
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_pair_card
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_oneDouble_count
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_twoDouble_count
-- SL4TMarkedFlagStratumDeformation.lean
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_le_comp
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.mul_remainderRowMinor_mem_pointInitialIdeal
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_evaluate_points
#print axioms VOA.DeligneAudit.SL4T.selectedSitePolynomial_dvd_product
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_characteristic
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_characteristic
#print axioms VOA.DeligneAudit.SL4T.zeroSitePolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.zeroSitePolynomial_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.sitePolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.sitePolynomial_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.selectedZeroFactor
#print axioms VOA.DeligneAudit.SL4T.selectedZeroFactor_dvd
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_deformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_markedDeformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_deformedMinor_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_remainderTopIdeal_le
#print axioms VOA.DeligneAudit.SL4T.singlyMarked_markedRemainderMinor_mem
#print axioms VOA.DeligneAudit.SL4T.doublyMarked_remainderTopIdeal_le
#print axioms VOA.DeligneAudit.SL4T.polynomialSubmoduleTopIdeal_power_eq
#print axioms VOA.DeligneAudit.SL4T.sup_eq_pointInitialIdeal_of_count
-- SL4TMarkedFlagStratumExactness.lean
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_le_markedFlagIdeal
#print axioms VOA.DeligneAudit.SL4T.quotientRoot_group_elementary
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_map_mk
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_quotientRoot_eq_bot
#print axioms VOA.DeligneAudit.SL4T.quotientRoot_list_length
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratum_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_le_stratumPoint
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumIdeal_map_span
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal_eq
-- SL4TMarkedFlagJointStratumCount.lean
#print axioms VOA.DeligneAudit.SL4T.quotient_map_finrank
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_jointStratum_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratum_finrank_of_eq
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_jointStratum_one_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_jointStratum_two_finrank
-- SL4TMarkedFlagEquivariantStrata.lean
#print axioms VOA.DeligneAudit.SL4T.stablePointAction
#print axioms VOA.DeligneAudit.SL4T.stablePointAction_equivariant
#print axioms VOA.DeligneAudit.SL4T.stablePointQuotient_fixed_finrank
#print axioms VOA.DeligneAudit.SL4T.deletedPositionPerm
#print axioms VOA.DeligneAudit.SL4T.deletedPositionPerm_spec
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedRelabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedPoint_relabel
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_relabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedDoubles_relabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedRelabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedPoint_relabel
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedSelectedDoubles_relabel
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint_stable
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint_stable
#print axioms VOA.DeligneAudit.SL4T.standardSites
#print axioms VOA.DeligneAudit.SL4T.standardSites_injective
#print axioms VOA.DeligneAudit.SL4T.standardSites_ne_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedStratumPoint_injective
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumPoint_injective
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratum_invariant_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratum_invariant_finrank
