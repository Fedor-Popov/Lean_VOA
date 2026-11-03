import VOA.DeligneAudit.D4CharRound105Audit
import VOA.DeligneAudit.D4CharMixedFour

/-!
# The mixed-Cauchy GL_5 to GL_4 down-step: declaration and axiom audit

This module imports `D4CharRound105Audit`, preserving the earlier `D4Char` and type-A
collision checks.

Axiom check: the printed theorems depend exactly on `[propext, Classical.choice, Quot.sound]`.

Proved, in namespace VOA.DeligneAudit.D4Char:
* DownReindex: gtPartitionsTwo enumerates every two-part partition of a fixed size.
  sum_gtRows_three_nat converts the complete integer interlacing set, and
  sum_gtDownRowsTwo_reverse reverses all branches by their nonnegative size gain.
* DownGP: gtDownTwo_transform applies proved gP after reversing branches;
  gtDownTwo_transform_pair applies it independently in both alphabets;
  gtDownTwo_transform_diagonal imposes equal gains with the full min(n,m) range.
* DownRegroup: gtMixedFive_ct_regroup is the actual GT-side constant-term identity
  at every remaining Laurent monomial and every homogeneous bidegree. It is the
  common-gain convolution of gtMixedFourHomCoeff with g_k(x) g_k(y).
* DownGamma: gtMixedGamma_isUnit and gtMixedGamma_convolution_cancel justify the
  paper's Gamma cancellation over any commutative coefficient ring.
* DownEuler, DownKernelCT: gtInvPoch_map supplies coefficient naturality;
  gtLastEuler_product_coeff retains the actual Laurent power of the deleted variable;
  gtLastEulerPair_ct and gtLastEulerPair_mul_ct identify the constant term of the
  actual four removed Euler factors as Gamma, including an arbitrary lower kernel.
* DownHomogeneous: gtMixed_five_homogeneous converts the proved four-degree stable
  identity to sums over all partitions of any two fixed sizes.
* DownCollapse, DownFourSeries: gtBiCollapseHom proves homogeneous substitution is
  multiplicative; gtFourCollapse_coeff identifies every coefficient explicitly;
  gtMixed_five_collapsed applies this actual ring homomorphism to gtMixedFiveKernel.
* DownRankKernel: gtMixedRankKernel is the same Euler product at ambient rank N;
  gtMixedRankKernel_five identifies it with the stable kernel;
  gtMixedRankKernel_collapsed_succ splits off its exact last-coordinate factors.
* DownUnit: gtMixedFiveSeries_branch_one applies full gP branching at auxiliary w = 1;
  gtMixedFiveKernel_branch_one removes the same four Euler factors on the kernel side.
  gtMixedExtra_isUnit proves these factors can be cancelled without a domain assumption.
* MixedFour: gtMixed_four and gtMixed_four_coeff prove MC_(2,2,4), in every homogeneous
  bidegree, for arbitrary q with Pochhammer units and arbitrary unit alphabets x,y,u.
  No extra coordinate hypothesis, coefficient comparison, or unproved identity is used.

## Conventions and the route
* gtMixedFourSeries has x-degree outermost and y-degree innermost. Its (n,m) coefficient
  is gtBiCoeff m n. The output of gtFourCollapse uses this same convention.
* The final proof uses full branching specialized at w = 1, cancelling the separable
  Euler unit. This is justified by gtDownTwo_transform_pair and retains all positive
  and negative size gains independently. It proves the needed down-step directly.
  The paper's constant-term/Gamma calculations are independently proved above, but
  are not dependencies of the final cancellation argument beyond shared infrastructure.
* The endpoint is a homogeneous generating-series identity at arbitrary unit
  alphabets. It immediately permits x = y = (x,x^-1), the substitution needed for K8.
  A separately packaged equality of four independent coefficient arrays at rank four
  is not declared; no such additional extraction is needed for that K8 specialization.

## Not proved here
* Lemma O for D4K.ctTheta (the all-index Rogers--Szego orthogonality identity) is not
  proved in this module; it is `rsMoment_orthogonal` in `D4CharRogersOrthogonal`.
* Specialization into D4K.S via D4K.jmap, identification with kernelM, and assembly with
  D4K.Ikernel_coeff_even and ev1_Cdem are not treated here.
* HilbertIdentity is not proved here; d4_hilbInt_eq_levi is not declared in this chain.
  GradedLeviBound and the fusion total bound are not treated.

## Remarks
* Do not treat an additive homogeneous coefficient operation as a ring map without
  proof: gtSum_antidiagonal_grid and gtBiCollapse_mul supply the required finite Fubini.
* Every reciprocal Pochhammer map must use gtInvPoch_map; the chosen unit witnesses
  do not make its naturality a definitional equality.
* Generic prod_range_succ rewriting may split the fixed rank-two numerator before
  the ambient-rank denominator. Specify n := N for gtRankXStep_succ.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) :
    gtMixedFourSeries q h x y u =
      gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedRankKernel q h u 4) := gtMixed_four q h x y u

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_ct_regroup
#print axioms VOA.DeligneAudit.D4Char.gtMixedGamma_convolution_cancel
#print axioms VOA.DeligneAudit.D4Char.gtLastEulerPair_mul_ct
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five_collapsed
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveSeries_branch_one
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernel_branch_one
#print axioms VOA.DeligneAudit.D4Char.gtMixed_four
#print axioms VOA.DeligneAudit.D4Char.gtMixed_four_coeff
