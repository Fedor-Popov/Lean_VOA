import VOA.DeligneAudit.D4CharRound106Audit
import VOA.DeligneAudit.D4CharThetaReindex

/-!
# Lemma O and the theta reduction of specialized mixed Cauchy: declaration and axiom audit

This module imports `D4CharRound106Audit` to retain the earlier `D4Char` and type-A namespace
collision checks.

Axiom check: every main theorem depends exactly on `[propext, Classical.choice, Quot.sound]`;
the coordinate helper rsZVector_eq uses `[propext, Quot.sound]`.

Proved, in namespace VOA.DeligneAudit.D4Char:
* ThetaBinomial: rsThetaSum_product is the finite Gaussian cancellation for the
  signed quadratic theta seed, for all n and all integer shifts. rsThetaSum_zero
  proves every interior root. The proof uses q-Pascal directly on the signed seed;
  rsThetaSeed_pred incorporates the two triangular-exponent shifts.
  No Jacobi product theorem, literature lemma, or finite numerical check is used.
* RogersMoments: rsH is the full Gaussian Laurent polynomial in the original
  D4K.xv coordinate. ctTheta_rsH and rsMoment_rsH prove all zero moments, including
  odd parity and the normalized initial value.
* RogersRecurrence: rsH_recurrence and rsH_recurrence_all prove the three-term
  recurrence, including the zero-index boundary, by Gaussian Pascal and lowering.
* RogersOrthogonal: rsMoment_orthogonal proves Lemma O for every k,l;
  ctTheta_rsH_mul is its statement directly on the original D4K.ctTheta.
  Off-diagonal vanishing is an induction; diagonal norms are exactly D4K.qpoch k.
* KernelScalars: rsJmap_injective proves injectivity of D4K.jmap.
  rsJmap_invPoch, rsJmap_eulerInv, rsJmap_eulerPos identify its exact denominator
  and Euler images. rsPochhammerUnits and rsInvPoch_R supply the actual Laurent
  coefficient-ring normalization, with no coefficient-field assumption.
* RogersGT: rsGT_two identifies every two-row GT P at the ordered alphabet (x,x^-1)
  with rsH (a-b). rsQ_two supplies the full Q normalization; rsMoment_Q_mul is
  orthogonality of the actual GT factors used in the proved mixed-Cauchy theorem.
* ThetaSpectators: rsMoment_gtEval_mul proves linearity over every ambient GL_4
  GT factor in the actual z coordinates. rsMoment_mixed_term performs the exact
  equal-gap cancellation with the remaining three inverse Pochhammer factors.
* KernelEuler: rsEulerInv_EInv and rsEulerPos_EPos identify every individual Euler
  factor with D4K.EInv and D4K.EPos, at arbitrary Laurent weights.
* MixedTheta: rsMixedKernel is the actual ring substitution of gtMixedRankKernel,
  into D4K.S, with x=y=(s*x,s/x) and u=z. rsMixedKernel_eq_series applies the proved
  MC_(2,2,4); rsMixedKernel_coeff expands all finite coefficients;
  rsMixedKernel_moment_coeff applies orthogonality; odd coefficients vanish.
* ThetaReindex: rsEqualGap_sum is the exhaustive partition-pair to triple bijection.
  rsMixedKernel_moment_even is the full three-index formula for every n, retaining
  all a+b+c=n and their GL_4 factors and inverse Pochhammer coefficients.

Lemma O is proved on D4K.ctTheta and applied to the complete specialized mixed-Cauchy
series, not merely packaged as an abstract orthogonality assumption.

## Not proved here
* The product identification
    rsMixedKernel = D4K.EPos 1 0 2 two_ne_zero * D4K.kernelM
  is not proved in this module (it is `rsMixedKernel_eq_kernelM`, audited in
  `D4CharRound108Audit`). All individual Euler identifications are proved in KernelEuler;
  the identification transports and groups the four numerator factors and sixteen
  denominator factors through the homogeneous ring substitution. The extra scalar
  (s^2;q) factor must be retained, rather than silently cancelled.
* Multiplying the theta series by D4K.EInv 1 0 2 two_ne_zero, using the Euler inverse
  identity, and assembling with D4K.Ikernel_coeff_even d4FiniteIdentity_holds turns the
  triple sum into the four-index q-multinomial character formula for Cdem.
* Applying ev1_Cdem, GT central shift, and the GT/gl4Hilb coefficient bridge gives
  HilbertIdentity, namely d4_hilbInt_eq_levi. That theorem is not declared or proved in
  this module (it is in `D4CharHilbertIdentity`), so the general hD squeeze is not claimed here.
* GradedLeviBound and the fusion total bound are not treated.

## Remarks
* The three-index theta formula for rsMixedKernel must not be cited as a Cdem identity
  without the product identification with kernelM times its extra Euler factor and the
  coefficient assembly.
* Naturals in gtMixedFourRow arguments elaborate as integers unless cast explicitly;
  preserve the natural subtraction n-a-b in the three-index finite sum.
* gtBiCollapseHom a b uses a for the inner degree and b for the outer degree.
  gtMixedFourSeries has positive degree outermost. Thus its antidiagonal pair t
  indexes positive partitions of t.2 and negative partitions of t.1.
* D4K.Kq's numeral nonzeroness is conveniently transported through HahnSeries.C;
  relying on norm_num alone does not discharge the coefficient two being nonzero.
-/

namespace VOA.DeligneAudit.D4Char

open DeligneCharacter

example (k l : ℕ) : D4K.ctTheta (rsH k * rsH l) =
    if k = l then (2 * D4K.qpoch k) • (1 : D4K.R) else 0 := ctTheta_rsH_mul k l

example : Function.Injective D4K.jmap := rsJmap_injective

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsThetaSum_product
#print axioms VOA.DeligneAudit.D4Char.rsMoment_rsH
#print axioms VOA.DeligneAudit.D4Char.rsH_recurrence_all
#print axioms VOA.DeligneAudit.D4Char.rsMoment_orthogonal
#print axioms VOA.DeligneAudit.D4Char.ctTheta_rsH_mul
#print axioms VOA.DeligneAudit.D4Char.rsJmap_injective
#print axioms VOA.DeligneAudit.D4Char.rsJmap_eulerPos
#print axioms VOA.DeligneAudit.D4Char.rsQ_two
#print axioms VOA.DeligneAudit.D4Char.rsMoment_mixed_term
#print axioms VOA.DeligneAudit.D4Char.rsEulerPos_EPos
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_eq_series
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_moment_odd
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_moment_even
