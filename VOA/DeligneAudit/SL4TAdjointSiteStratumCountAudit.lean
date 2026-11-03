import VOA.DeligneAudit.SL4TMarkedFlagEquivariantAudit
import VOA.DeligneAudit.SL4TAdjointSiteStratumReduction

/-!
# Toward `OneAdjointStratumCount B 1`: reduction to the low strata, declaration and axiom audit

**Status.** For every `B` and `k`, `OneAdjointStratumCount B k` and Law B at one adjoint site
follow from `dim A ≤ w₀` and the stratum inequalities `dim A/G_j ≤ w₀ - w_j` for
`1 ≤ j ≤ k + [(d₁, d₃) = (1, 0)]` only (`oneAdjointStratumCount_of_low_strata`,
`adjointSiteLawB_of_low_strata`). Above that bound no site word has `j` T-states
(`adjointSiteWordCount_eq_zero_of_lt`), so the inequality is `dim A/G_j ≤ dim A ≤ w₀`. For
`k = 1` the remaining strata are `j = 1` on every block and `j = 2` on the doubly marked blocks.
Also: the joint ideal vanishes above the number of selected roots
(`adjointSiteJointTopIdeal_eq_bot_of_lt`).

**Not proved here.** `OneAdjointStratumCount B 1`, `oneAdjointStratumCount_one` and
`adjointSiteLawB_one` are not proved. Its parts:

* proved: the strata with `j` above the T-bound (`oneAdjointStratumCount_of_low_strata`);
  conjunct 3 (`adjointSiteJointTopIdeal_eq_sup`); the flag level, equivariantly, for generic `Y`
  (`SL4TMarkedFlagEquivariantAudit`);
* open: the flag-level edge cases (`Y = ∅`, `Z = ∅`, `|Y| < 2`, `U` or `V = ∅`);
  (a) `#orbits(X_{<j}) = w₀ - w_j` (colour profile per site);
  (b) the surjection `C^H ↠ AdjointSiteCoefficientRing q (B - 1)`;
  (c) `(G_j)^H ↦ adjointSiteJointTopIdeal`.
-/

#print axioms VOA.DeligneAudit.SL4T.polynomialSubmoduleTopIdeal_eq_bot_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteJointTopIdeal_eq_bot_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le_of_block
#print axioms VOA.DeligneAudit.SL4T.adjointSiteTBound
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordTCount_le_bound
#print axioms VOA.DeligneAudit.SL4T.adjointSiteWordCount_eq_zero_of_lt
#print axioms VOA.DeligneAudit.SL4T.adjointSiteQuotient_finrank_le
#print axioms VOA.DeligneAudit.SL4T.oneAdjointStratumCount_of_low_strata
#print axioms VOA.DeligneAudit.SL4T.adjointSiteLawB_of_low_strata
