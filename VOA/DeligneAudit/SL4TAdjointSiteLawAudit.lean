import VOA.DeligneAudit.SL4TMultiDoubledCompletionAudit
import VOA.DeligneAudit.SL4TAdjointSiteRingKernel

/-!
# Law B at one adjoint site: declaration and axiom audit

Target (not proved here). For `k ≥ 1` and `B ≥ 2k`,

    AdjointSiteLawB B k :
      dim W(θ + B ω₂, B - k + 1) / ⟨f₂(B - k) v⟩ ≤ 15 · 20^k · 6^(B - 2k),

with the case `k = 1` the statement (III). The conditional theorem
`adjointSiteLawB_of_residuals` is recorded here only as the proposition
`AdjointSiteLawBFromResiduals B k := OneAdjointStratumCount B k → ZeroAdjointFlatRelation B k →
AdjointSiteLawB B k`; its assembly is not part of the files audited here (see
`SL4TAdjointSiteAssemblyAudit` and `SL4TAdjointSiteJointFlagAudit`).

Proved, by file:
* `SL4TAdjointSiteModule`: the presentation `adjointSiteSpec B h` (the `truncatedWeylSpec`
  relations at weight `(1, B, 1)` and cutoff `h + 1`, plus `f₂(h) v = 0`), the module
  `AdjointSiteModule B h`, its universal property `adjointSiteSpec_sat_iff`, the cutoff on the
  whole module, finite-dimensionality, the cyclic reformulation, and the target `AdjointSiteLawB`.
* `SL4TAdjointSiteTransportedRelations`: Lemma T, `adjointSite_transported_relations`:
  `q(h) F v = 0` and `z(h) x F v = 0`, from the local Weyl relations and `f₂(h) v = 0` only.
* `SL4TAdjointSiteLevelOneRelations`: positive power sums vanish in `H(d, 1)`, `d ≤ 1`
  (`grassmannianPowerSum_label_one`); the outer alphabet currents act by zero on the first Levi
  multiplicities (`radicalAlphabetQuotCurrent_outer_eq_zero`); the level-1 alphabet bound
  `x y^n z(r) v ∈ M_{>(1,n,1)}` for `r ≥ 1` (`adjointSite_shiftedTopWord_mem`); Lemma E,
  `adjointSite_lowerKey_mem`: `(n+1) x y^n z z(h) v ∈ M_{>(1,n+1,1)}`.
* `SL4TAdjointSiteLevelTwoRelations`: Proposition J,
  `adjointSite_highModeCompound_mem_higherSecondLevi`:
  `q(h) g^E x y^(n+1) z v ∈ W_{>((1,n+1,1),(E,1))}` for every `E`.
* `SL4TAdjointSiteResiduals`: the ring kernel `adjointSiteKernelIdeal` (`I_J(h)`), the coefficient
  ring `A = R / I_J(h)`, `P_y`, the joint symbol `s`, the joint and pure top-row ideals `G_j`,
  `G_j(L)`, the site words and `w_j(d,e)`, the two residual propositions
  `OneAdjointStratumCount` (S_A) and `ZeroAdjointFlatRelation` (L₂), and the site
  count, `adjointSiteWord_weight_sum`: `Σ_words 3^T 2^D = 15 · 20^k · 6^(B - 2k)`.
* `SL4TAdjointSiteRingKernel`: the `[d₁ = 0] J_h(g₁)` term of Corollary K,
  `adjointSite_middleAlphabetTail_le_kernel`.

Not proved in the files audited here (they are proved in the files audited by
`SL4TAdjointSiteAssemblyAudit`): Theorem J₃¹(h) as the ideal statement
`J_h(g₂) ⊆ ker π̄` on the blocks over `(1, d, 1)` (it needs Lemma CI(i), Cartan generation at one
adjoint site, and Lemma M(ii) on the second Levi closure; Proposition J is its zero-mode input);
the terms `J_h(x₂)` and `[d₃ = 1] J_h(g₂)` of Corollary K (the latter via `J₃⁰` and `J₃¹`);
Theorem L₃(h); the `(0, ·, 1)` relation from Σ₁ at general `h`; and the assembly.

Axiom check: the 91 explicit declarations of the six content files are printed below: 80
depend on exactly `[propext, Classical.choice, Quot.sound]`, six on `[propext, Quot.sound]` and
five on none. No `sorry`, `admit`, `native_decide` or additional axiom is used.
-/

-- SL4TAdjointSiteModule.lean
#print axioms VOA.DeligneAudit.SL4T.adjointSiteSpec
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteModule
#print axioms VOA.DeligneAudit.SL4T.adjointSiteRep
#print axioms VOA.DeligneAudit.SL4T.adjointSiteGenerator
#print axioms VOA.DeligneAudit.SL4T.adjointSiteSpec_sat_iff
#print axioms VOA.DeligneAudit.SL4T.adjointSite_relations
#print axioms VOA.DeligneAudit.SL4T.adjointSite_localWeyl
#print axioms VOA.DeligneAudit.SL4T.adjointSiteModule_current_zero
#print axioms VOA.DeligneAudit.SL4T.adjointSiteModule_finite_and_local_bound
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteLawB
#print axioms VOA.DeligneAudit.SL4T.adjointSiteModule_rank_iff_cyclic
-- SL4TAdjointSiteTransportedRelations.lean
#print axioms VOA.DeligneAudit.SL4T.op_comm_of_single_bracket
#print axioms VOA.DeligneAudit.SL4T.op_comm_of_zero_bracket
#print axioms VOA.DeligneAudit.SL4T.bracket_last_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_last_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_first_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_middle_first
#print axioms VOA.DeligneAudit.SL4T.bracket_last_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_last_first
#print axioms VOA.DeligneAudit.SL4T.bracket_last_highest
#print axioms VOA.DeligneAudit.SL4T.bracket_first_highest
#print axioms VOA.DeligneAudit.SL4T.bracket_first_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_highest_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_first_last
#print axioms VOA.DeligneAudit.SL4T.bracket_highest_last
#print axioms VOA.DeligneAudit.SL4T.lowering_square_of_label_one
#print axioms VOA.DeligneAudit.SL4T.adjointSite_transported_relations
-- SL4TAdjointSiteLevelOneRelations.lean
#print axioms VOA.DeligneAudit.SL4T.complete_one
#print axioms VOA.DeligneAudit.SL4T.eClass_label_one
#print axioms VOA.DeligneAudit.SL4T.grassmannianPowerSum_label_one
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianPowerSum_outer_eq_zero
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetQuotCurrent_outer_eq_zero
#print axioms VOA.DeligneAudit.SL4T.adjointSite_topWord_mem_layer
#print axioms VOA.DeligneAudit.SL4T.op_pow_comm_of_zero_bracket
#print axioms VOA.DeligneAudit.SL4T.last_compoundPower_comm
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_last_comm_other
#print axioms VOA.DeligneAudit.SL4T.radicalAlphabetCurrent_topWord
#print axioms VOA.DeligneAudit.SL4T.adjointSite_shiftedTopWord_mem
#print axioms VOA.DeligneAudit.SL4T.adjointSite_lowerKey_mem
-- SL4TAdjointSiteLevelTwoRelations.lean
#print axioms VOA.DeligneAudit.SL4T.leviLast_middle_comm
#print axioms VOA.DeligneAudit.SL4T.leviCompound_middle_comm
#print axioms VOA.DeligneAudit.SL4T.leviCompound_middlePower_comm
#print axioms VOA.DeligneAudit.SL4T.leviLast_middlePower_comm
#print axioms VOA.DeligneAudit.SL4T.bracket_highest_highest
#print axioms VOA.DeligneAudit.SL4T.adjointSite_topWord_mem_image
#print axioms VOA.DeligneAudit.SL4T.adjointSite_topWord_lastLowering_zero
#print axioms VOA.DeligneAudit.SL4T.adjointSite_highModeCompound_mem_higherSecondLevi
-- SL4TAdjointSiteResiduals.lean
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetModeTailIdeal
#print axioms VOA.DeligneAudit.SL4T.adjointSiteKernelIdeal
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteCoefficientRing
#print axioms VOA.DeligneAudit.SL4T.adjointSiteCharacteristic
#print axioms VOA.DeligneAudit.SL4T.adjointSiteFlatSymbol
#print axioms VOA.DeligneAudit.SL4T.adjointSiteMarkedSymbol
#print axioms VOA.DeligneAudit.SL4T.adjointSiteJointSymbol
#print axioms VOA.DeligneAudit.SL4T.adjointSiteJointSubmodule
#print axioms VOA.DeligneAudit.SL4T.adjointSitePowerSubmodule
#print axioms VOA.DeligneAudit.SL4T.adjointSiteJointTopIdeal
#print axioms VOA.DeligneAudit.SL4T.adjointSiteRemainderTopIdeal
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteState
#print axioms VOA.DeligneAudit.SL4T.DoubledSiteState
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteWord
#print axioms VOA.DeligneAudit.SL4T.adjointSiteUColour
#print axioms VOA.DeligneAudit.SL4T.adjointSiteVColour
#print axioms VOA.DeligneAudit.SL4T.adjointSiteStateColourCount
#print axioms VOA.DeligneAudit.SL4T.doubledSiteStateColourCount
#print axioms VOA.DeligneAudit.SL4T.flagColourInY
#print axioms VOA.DeligneAudit.SL4T.adjointSiteStateYCount
#print axioms VOA.DeligneAudit.SL4T.doubledSiteStateYCount
#print axioms VOA.DeligneAudit.SL4T.siteYWeight
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordColourCount
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordBlock
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordCount
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordWeight
#print axioms VOA.DeligneAudit.SL4T.adjointSiteState_weight_sum
#print axioms VOA.DeligneAudit.SL4T.doubledSiteState_weight_sum
#print axioms VOA.DeligneAudit.SL4T.simpleSiteState_weight_sum
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWord_weight_sum
#print axioms VOA.DeligneAudit.SL4T.OneAdjointStratumCount
#print axioms VOA.DeligneAudit.SL4T.ZeroAdjointFlatRelation
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteLawBFromResiduals
-- SL4TAdjointSiteRingKernel.lean
#print axioms VOA.DeligneAudit.SL4T.bracket_middle_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_middle_highest
#print axioms VOA.DeligneAudit.SL4T.positionModeProduct_apply_eq_zero
#print axioms VOA.DeligneAudit.SL4T.leviMiddle_middle_commute
#print axioms VOA.DeligneAudit.SL4T.leviMiddle_compound_commute
#print axioms VOA.DeligneAudit.SL4T.middleLowering_kills_radicalLayer
#print axioms VOA.DeligneAudit.SL4T.adjointSite_middleLowering_kills_image
#print axioms VOA.DeligneAudit.SL4T.adjointSite_secondLevi_middlePower_zero
#print axioms VOA.DeligneAudit.SL4T.adjointSite_middleAlphabet_mode_zero
#print axioms VOA.DeligneAudit.SL4T.adjointSite_middleAlphabetTail_le_kernel
