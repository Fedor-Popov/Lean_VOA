import VOA.DeligneAudit.SL4TMarkedFlagStrataAudit
import VOA.DeligneAudit.SL4TUnmarkedFlagStrata
import VOA.DeligneAudit.SL4TSinglyMarkedOmittedPointStratum

/-!
# Stratum counts of the marked full flags at one adjoint site: declaration and axiom audit

**Status.** This audit extends `SL4TMarkedFlagStrataAudit` with:

* layer isomorphisms for every layer used by the stratum recursions
  (`SL4TMarkedFlagLayerIsomorphisms`):
  - the doubly marked ring without doubles, a first-group root: the zero layer is the singly
    marked ring, the positive layers the doubly marked ring with cutoff lowered by one
    (`doublyMarkedZeroLayer_finrank_eq_bound`, `doublyMarkedZeroLayerMap_injective_singly`,
    `doublyMarkedZeroLayerMap_injective_lower`);
  - the doubly marked ring with doubles: all four kinds of layer of a first-group root
    (`doublyMarkedLayerMap_injective_weak`, `_same`, `_singlyProduct`, `_lower`); the product
    of the remaining first-group roots in the singly marked child has exactly the dimension of
    the unmarked product bound (`doublyMarkedLayer_childProduct_finrank_eq`);
  - the weak ring with doubles: exact layers of a weak root (`weakLayer_finrank_eq_bound`) and
    the four layer isomorphisms (`weakLayerMap_injective_weak`, `_singly`, `_lower`,
    `_doubly`);
* the unmarked full flags as marked flags without marked groups (`unmarkedFlagIdeal`,
  `unmarkedFlagIdeal_eq`, `unmarkedFlag_finrank_eq`), their exact layers and layer isomorphisms
  (`unmarkedLayer_finrank_eq_bound`, `unmarkedLayerMap_injective_same`,
  `unmarkedLayerMap_injective_lower`), and the first product strata
  (`SL4TUnmarkedFlagStrata`):
  - without doubles, `dim (∏ Z) ≥ (n - |Z|) (n - 1)!`
    (`unmarkedFlag_noDouble_product_finrank_ge`);
  - with one double, `dim (∏ Z) ≥ C(n - |Z|, 2) (n - 2)!`
    (`unmarkedFlag_oneDouble_product_finrank_ge`);
  - the generic product step over the positive layers of a root of `Z`
    (`productStratum_layers_le`).

* preparatory coefficient lemmas for the omitted-point stratum
  (`SL4TSinglyMarkedOmittedPointStratum`: `groupSubtopCoefficient`, `coeff_mul_top_sub_one`); the
  omitted-point stratum bound itself is not proved here.

**Not proved here.** `OneAdjointStratumCount B 1` is open in this module.

Axioms of every declaration are printed below.
-/

-- SL4TMarkedFlagLayerIsomorphisms.lean
#print axioms VOA.DeligneAudit.SL4T.deletedLayerMap_injective_of_finrank_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayerBound
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayer_child_singly_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayer_child_lower_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayer_finrank_le_bound
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayerBound_sum
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayer_finrank_eq_bound
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayerMap_injective_singly
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedZeroLayerMap_injective_lower
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerMap_injective_weak
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerMap_injective_same
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerMap_injective_lower
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayer_childProduct_finrank_eq
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerMap_injective_singlyProduct
#print axioms VOA.DeligneAudit.SL4T.weakLayerBound
#print axioms VOA.DeligneAudit.SL4T.weakLayer_child_weak_le
#print axioms VOA.DeligneAudit.SL4T.weakLayer_child_singly_le
#print axioms VOA.DeligneAudit.SL4T.weakLayer_child_lower_le
#print axioms VOA.DeligneAudit.SL4T.weakLayer_child_doubly_le
#print axioms VOA.DeligneAudit.SL4T.weakLayer_finrank_le_bound
#print axioms VOA.DeligneAudit.SL4T.weakLayerBound_sum
#print axioms VOA.DeligneAudit.SL4T.weakLayer_finrank_eq_bound
#print axioms VOA.DeligneAudit.SL4T.weakLayerMap_injective_weak
#print axioms VOA.DeligneAudit.SL4T.weakLayerMap_injective_singly
#print axioms VOA.DeligneAudit.SL4T.weakLayerMap_injective_lower
#print axioms VOA.DeligneAudit.SL4T.weakLayerMap_injective_doubly
-- SL4TUnmarkedFlagStrata.lean
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlagIdeal
#print axioms VOA.DeligneAudit.SL4T.UnmarkedFlagRing
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_finite
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlagIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_finrank_eq
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_elementary
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_cutoff
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_same_le_ker
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayerBound
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_child_same_eq
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_child_lower_eq
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_finrank_le_bound
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayer_finrank_eq_bound
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayerMap_injective_same
#print axioms VOA.DeligneAudit.SL4T.unmarkedLayerMap_injective_lower
#print axioms VOA.DeligneAudit.SL4T.prod_eq_mul_deletedGroup_of_mem
#print axioms VOA.DeligneAudit.SL4T.productStratum_layers_le
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_noDouble_product_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.unmarkedFlag_oneDouble_product_finrank_ge
-- SL4TSinglyMarkedOmittedPointStratum.lean
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient
#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_map
#print axioms VOA.DeligneAudit.SL4T.groupSubtopCoefficient_map
#print axioms VOA.DeligneAudit.SL4T.coeff_mul_top_sub_one
