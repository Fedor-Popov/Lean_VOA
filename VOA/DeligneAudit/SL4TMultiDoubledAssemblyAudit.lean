import VOA.DeligneAudit.SL4TMultiDoubledRankAudit
import VOA.DeligneAudit.SL4TMultiDoubledAssembly
import VOA.DeligneAudit.SL4TInvariantIdealContraction
import VOA.DeligneAudit.SL4TFullFlagGradedCertificate

/-!
# All-tail multiplicity descent, stable coefficient flags, and multi-doubled Levi assembly

The concrete Cartan factorization uses `middleFlagAllTailIdeal q N`, the supremum of
all four-block power-sum ideals in modes at least `N`. It is killed, together with every
multiple, by the actual second Levi evaluation for every positive cutoff. The descended
map `middleFlagAllTailEvaluation` remains surjective. This is the full tail ideal rather
than the single-mode ideal.

`pi_subspaceFlag_bound` proves the current-module cell bound for subspaces stable under
positive power sums. The coefficient corrections need only lie in the earlier subspace;
they need not generate an ideal. The characteristic relation is supplied by Garland, and
nilpotence forces every positive Cartan to vanish on each one-dimensional quotient.
Zero levels are included. `mixedQuotientRingImage_bound_of_subspaceFlag` instantiates this
on any killed quotient of the actual mixed coefficient ring, with its proved Newton
identities and nilpotence.

`multiDoubledSiteCellCatalog k n` enumerates all double-site words followed by all simple
sites, retaining their content and multiplicity. The balanced sum is `20 ^ k * 6 ^ n`
for every `k, n`. Partitioning by valid content gives
`multiDoubledSiteBlockBound_sum_all_valid`, and the actual nested Levi indices give
`multiDoubledSiteNestedBlockBound_sum_le`.

The endpoint `truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags` has exactly the intended
module `TruncatedLabelModule 0 B 0 (B - k)` and the intended bound for all `2 * k <= B`.
It remains conditional on

    forall q in mixedValidBlocks 0 B, MultiDoubledSiteCoefficientFlag B k q.

`MultiDoubledSiteCoefficientFlag` is the nonemptiness of an explicit finite subspace flag
in `MixedRing q` modulo `middleFlagAllTailIdeal q (B - k)`, with positive-power-sum
stability, relative characteristic/truncation relations, and weighted cost at most the
word count. This hypothesis is not discharged here. The universal zero-cutoff
boundary is handled by the local bound when `k = 0`.

The invariant descent statements are proved for every finite group of complex-algebra
automorphisms. Averaging is a projection linear over fixed coefficients. A surjective
equivariant algebra map is surjective on fixed algebras; the fixed-source quotient by its
contracted kernel is the fixed target. Invariant-generated ideals contract exactly, and
adding their extensions to any stable ideal commutes with contraction. These theorems do
not assume a dimension formula. Their specialization to the Young subgroup and the
identification of its contracted root-power ideal with the four-block tail ideal remain
unproved here.

`fullFlag_remainderTopIdeal_strict_certificate` instantiates the graded top-ideal result
on `FullFlagRing B N`, with homogeneity of its defining elementary and root-power ideal
proved. It retains the strictly larger correction degrees and includes the empty minor.
This is a concrete full-flag certificate, not a certificate in the partial-flag ring.

## Proved and not proved here
* The all-mode Cartan factorization, power-sum-stable cell theorem, all-parameter word count,
  and conditional assembly on the actual Levi modules are proved.
* Not proved: the invariant algebra of the truncated full flag is not identified with
  `MixedRing q` modulo `middleFlagAllTailIdeal q N` for zero outer label. This requires the
  block-symmetric presentation and the contraction of the pure root-power ideal to the
  block power sums in all modes at least `N`.
* The partial-flag stratum orbit-count bounds are not proved. The scalar theorem
  `fullFlagStratumRankBound` gives total dimension, not invariant character. Averaging
  exactness and all-row/top-row equality do not supply that missing character information.
  An equivariant spanning argument would suffice for upper bounds. Alternatively the
  configuration deformation and associated-graded comparison can establish the invariant
  character, as in the paper. The top-row equality alone does not eliminate this use of
  the deformation argument.
* Not proved: the strict degree certificate is not transported to the partial-flag
  quotient, and its determinantal ideals are not refined by degree and bases into the explicit
  `MultiDoubledSiteCoefficientFlag`; the generic subspace-flag consumer is in place.
* Consequently `truncatedWeyl_sl4_multiDoubledSite_rank_le` is not defined or proved here.
  Only the conditional theorem with the `_of_flags` suffix is proved.

The module-theoretic assembly and the word count need no further unproved input once
`MultiDoubledSiteCoefficientFlag` is supplied; what is missing is the concrete Young-subgroup
presentation and the stratum invariant dimension bounds.

This audit imports `SL4TMultiDoubledRankAudit` and every content module of this layer.
Axiom check: no `sorryAx` occurs. Every explicit declaration is inventoried below by source
file and axiom print.
For every theorem and for the other definitions except the two catalog definitions,
the exact output is `[propext, Classical.choice, Quot.sound]`.
`multiDoubledSiteCellCatalog` and `multiDoubledSiteBlockBound` each print `[propext]`.
No additional axiom is introduced to make the definition inventories match theorem audits.
-/

-- SL4TMiddleFlagAllTails.lean
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailIdeal_le_allTail
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_antitone
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_le_annihilator
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailIdeal_le_kernel
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailEvaluation
#print axioms VOA.DeligneAudit.SL4T.middleFlagAllTailEvaluation_surjective

-- SL4TMultiDoubledCount.lean
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_mass
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_valid
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_weight
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCellCatalog_balanced
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSite_balanced_sum
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteBlockBound
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteBlockBound_sum_all_valid
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteFiber_balanced_sum

-- SL4TPowerSumStableFlag.lean
#print axioms VOA.DeligneAudit.SL4T.subspace_cell_nilpotent_mul
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_subspace
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_subspace_cell
#print axioms VOA.DeligneAudit.SL4T.subspaceFlag_eq_prefix
#print axioms VOA.DeligneAudit.SL4T.pi_subspaceFlag_bound_of_characteristic
#print axioms VOA.DeligneAudit.SL4T.pi_subspaceFlag_bound

-- SL4TMixedQuotientSubspaceFlag.lean
#print axioms VOA.DeligneAudit.SL4T.MixedQuotientSubspaceFlag
#print axioms VOA.DeligneAudit.SL4T.MultiDoubledSiteCoefficientFlag
#print axioms VOA.DeligneAudit.SL4T.mixedQuotientRingImage_bound_of_subspaceFlag

-- SL4TMultiDoubledOrbit.lean
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteSecondLeviOrbit_bound_of_flag

-- SL4TMultiDoubledAssembly.lean
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteNestedBlockBound_sum_le
#print axioms VOA.DeligneAudit.SL4T.multiDoubledSiteCyclic_rank_le_of_flags
#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_multiDoubledSite_rank_le_of_flags

-- SL4TInvariantDescent.lean
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedSubalgebra
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_fixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_id
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mul_fixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_map
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap_surjective
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedMap_kernel
#print axioms VOA.DeligneAudit.SL4T.finiteActionFixedQuotientEquiv

-- SL4TInvariantIdealContraction.lean
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverageToFixed
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverageToFixed_mul
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mem_ideal
#print axioms VOA.DeligneAudit.SL4T.finiteActionIdeal_comap_map
#print axioms VOA.DeligneAudit.SL4T.finiteActionInvariantGenerators_contract
#print axioms VOA.DeligneAudit.SL4T.finiteActionAverage_mem_stableIdeal
#print axioms VOA.DeligneAudit.SL4T.finiteActionIdeal_comap_sup_map

-- SL4TFullFlagGradedCertificate.lean
#print axioms VOA.DeligneAudit.SL4T.homogeneous_set_span_component_mem
#print axioms VOA.DeligneAudit.SL4T.elementarySymmetric_standardWeight
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_component_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlag_remainderTopIdeal_strict_certificate

