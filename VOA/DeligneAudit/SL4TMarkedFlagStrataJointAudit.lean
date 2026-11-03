import VOA.DeligneAudit.SL4TMarkedFlagStrataLowerAudit
import VOA.DeligneAudit.SL4TDoublyMarkedOneDoubleStrata

/-!
# Every stratum lower bound of the marked full flags with one double: declaration and axiom audit

**Status.** Every stratum lower bound that the one-adjoint-site ring statement needs on the marked
full flags with one double is a Lean theorem, for all parameters. Notation: a set `Y` of roots
with complement `Z`; `U = Vᶜ` the first group, `V` the marked group; `a = |U ∩ Y|`,
`b = |V ∩ Y|`, `c = |V ∖ Y|`, `d = |U ∖ Y|`; `c(Z)` the subleading coefficient of `∏_Z (1 - x t)`.

* Singly marked flag on `m + 2` roots, cutoffs `m` on `U` and `m + 1` on `V`, `m ≥ 1`:
  `dim (∏ Z, ∏ (V ∩ Y) · c(Z)) ≥ (b C(a + b - 1, 2) + c C(a + b, 2)) (m - 1)!`
  (`singlyMarkedFlag_oneDouble_stratum_finrank_ge`).
* Singly marked flag without doubles on `n` roots with `U ⊆ Y`:
  `dim (∏ Z) ≥ b (n - 1)!` (`singlyMarkedFlag_omittedZero_finrank_ge`).
* Doubly marked flag without doubles on `m + 2` roots: `dim (∏ Z) ≥ a b m!`
  (`doublyMarkedFlag_zeroPair_finrank_ge`).
* Weak flag on `m + 2` roots with one double, `m ≥ 1`:
  `dim (∏ Z) ≥ a b m! + (b C(b - 1, 2) + c C(b, 2)) (m - 1)!`
  (`weakMarkedFlag_stratum_finrank_ge`).
* The singly marked flag `S` with one double modulo `π = ∏ U` (`singlyMarkedProductIdeal`): its
  dimension (`singlyMarkedProduct_finrank_add`), its exact layers
  (`singlyProductLayerMap_injective_zero`, `singlyProductLayerMap_injective_lower`), and the stratum
  bound `dim (G + πS)/πS ≥ (b (C(a, 2) + a (b - 1)) + c (C(a, 2) + a b)) (m - 1)!`
  (`singlyMarkedProduct_stratum_finrank_ge`).
* Doubly marked flag on `m + 3` roots with one double, `m ≥ 1`:
  `dim (∏ Z, c(Z)) ≥ (a b C(m + 1, 2) + (a c + d b) C(a + b - 1, 2) + d c C(a + b, 2)) (m - 1)!`
  (`doublyMarkedFlag_oneDouble_stratum_finrank_ge`) and
  `dim ((∏ Z)²) ≥ a b C(a + b - 2, 2) (m - 1)!` (`doublyMarkedFlag_twoDouble_stratum_finrank_ge`).
  The two groups are interchangeable (`doublyMarkedFlagIdeal_compl`).

Each right side counts the configurations with the required number of points carrying at least
two roots, all in `Y`.

**Not proved here.** `OneAdjointStratumCount B 1` remains open. Open nodes:

* the complement form of the joint top-row minor ideals on the marked full flags (that the
  ideals bounded above are the top-row minor ideals of `t^(h+1)`, `s t^h` modulo `P_Y`);
* the deformation lower bound for the stratum quotients, as an equivariant identification of each
  stratum quotient with the graded configuration ring of the configurations with fewer T-points;
* the presentation of `AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - 1)` as
  the colour-invariant marked full flag, the identification of the descended ideals with
  `adjointSiteJointTopIdeal`, the joint-ideal equation `G_j = G_j(h+1) + s G_j(h)`, and the orbit
  count `adjointSiteWordCount`.

Axioms of every declaration are printed below.
-/

-- SL4TSinglyMarkedOneDoubleStratum.lean
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlagIdeal_univ_eq_unmarked
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_sdiff
#print axioms VOA.DeligneAudit.SL4T.stratumCard_sum_le
#print axioms VOA.DeligneAudit.SL4T.stratumPair_deleted_mul_mem
#print axioms VOA.DeligneAudit.SL4T.stratumPair_deleted_eq_of_mem
#print axioms VOA.DeligneAudit.SL4T.stratumPair_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount
#print axioms VOA.DeligneAudit.SL4T.stratumChoose_two_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.factorial_mul_pred_of_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_oneDouble_stratum_finrank_ge
-- SL4TMarkedFlagZeroPointStrata.lean
#print axioms VOA.DeligneAudit.SL4T.compl_inter_card_add_inter_card
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_omittedZero_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_zeroPair_finrank_ge
-- SL4TWeakMarkedFlagStratum.lean
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlagIdeal_univ_eq_unmarked
#print axioms VOA.DeligneAudit.SL4T.productStratum_layers_le_succ
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_stratum_finrank_ge
-- SL4TSinglyMarkedProductLayers.lean
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductIdeal
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_finite
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductFactor
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProductFactor_root
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_product_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_compl_product_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_unmarked_cutoff
#print axioms VOA.DeligneAudit.SL4T.deletedLayer_le_ker_map
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_same_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_finrank_add
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayer_finrank_eq
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayerMap_injective_zero
#print axioms VOA.DeligneAudit.SL4T.singlyProductLayerMap_injective_lower
-- SL4TSinglyMarkedMixedDoubleStratum.lean
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_zero_left
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_eq_add_mixed
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_stratum_finrank_ge
-- SL4TDoublyMarkedOneDoubleStrata.lean
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_compl_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_compl
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyStratum_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.childSingleton_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.aeval_prod_sq
#print axioms VOA.DeligneAudit.SL4T.mk_prod_sq
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_eq_one_of_deleted_empty
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneDoubleCount
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount_succ
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedResidualCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneDoubleCount_symm
#print axioms VOA.DeligneAudit.SL4T.choose_two_mul_factorial_eq_card
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_oneDouble_stratum_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_twoDouble_stratum_finrank_ge
