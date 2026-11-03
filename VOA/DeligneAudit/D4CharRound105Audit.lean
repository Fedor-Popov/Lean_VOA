import VOA.DeligneAudit.D4CharRound104Audit
import VOA.DeligneAudit.D4CharMixedDownCT

/-!
# Stable mixed Cauchy and the exact down-step branching formula: declaration and axiom audit

This module imports `D4CharRound104Audit` (with the type-A collision checks) together with
the results below.

Axiom check: of the 59 printed theorem audits, 58 depend exactly on
`[propext, Classical.choice, Quot.sound]`; the elementary row-index injectivity helper uses
`[propext, Quot.sound]`. All main theorems use exactly the three standard axioms. No `sorry`
or other proof escape is used.

Proved, in namespace VOA.DeligneAudit.D4Char:
* MixedTwoCoeff: gtTwoWeight_eOne, gtTwoWeight_eTwo, gtMixedTailAction_coeff extract
  both negative-block degrees directly from reciprocal Pochhammer identities.
  All integer boundary cases are included, with no field or domain assumption.
* MixedWeight: gtMixedWeight_subsets is X times Y after extracting both y degrees,
  on every integer output row. The preceding B calculation kills bad middle rows.
* MixedSlice: gtMixedSlice is the finite free row combination in integer degrees.
  Its support contains every valid row; negative degrees vanish by interlacing.
  gtMixedSlice_eval identifies it exactly with gtMixedFiveCoeff.
* MixedSliceShift: gtMixedSlice_shift_subsets and gtMixedSlice_shift_card prove
  the complete homogeneous shift on the finite free module of GL_5 rows.
* MixedFiveShift: gtMixedFive_shift : GTMixedFiveShift q h u holds with no hypotheses.
  gtMixedFiveCoeff_eq uses recurrence uniqueness with no GT-shift hypothesis.
* MixedEulerCoeff, MixedBiSeries, MixedFiveKernel: the actual Euler product has
  the matching four-degree recurrence, x symmetry and negative-only C(2,5) base.
* MixedFive: gtMixed_five and gtMixed_five_coeff prove MC_(2,2,5), for every
  quadruple of formal-variable degrees. The kernel is an iterated power series,
  with variables ordered outermost to innermost as x_2, x_1, y_2, y_1. Its factors
  are the two negative inverse Euler products and one mixed Euler step for each x.
  No shift, coefficient comparison, positivity or unproved identity is assumed.
* MixedDownBranch: gtMixedFour_mem_five and sum_gtMixedFiveRows identify the full
  GL_5 interlacing set with the product of the two GL_3 interlacing sets.
  gtMixedFive_psi_factor proves the coefficient factorization, using GT duality on
  the negative block. gtMixedFive_branching records the exact fifth-variable power.
* MixedDownCT: gtMixedFive_last_zero_coeff proves the actual fifth-variable
  constant-term formula on every Laurent monomial whose fifth coordinate is zero.
  Precisely the branches with equal positive and negative size gains survive;
  gtMixedFive_branch_gains_nonneg proves both gains are nonnegative.

Not proved here:
* GTMixedFiveShift and stable MC_(2,2,5) are proved (above).
* The N = 5 to N = 4 down-step is not complete. It requires applying
  gtMixedFive_last_zero_coeff to the stable identity, regrouping by the common
  nonnegative gain k, and using gtGP_two_branching in both two-variable alphabets, then
  identifying the matching Euler-kernel constant term and cancelling the common unit
  Gamma = sum_k g_k(x) g_k(y). No MC_(2,2,4) theorem is claimed here.
* Lemma O on D4K.ctTheta, specialization via D4K.jmap, and assembly using
  D4K.Ikernel_coeff_even and ev1_Cdem are not proved in this chain.
* HilbertIdentity is open; d4_hilbInt_eq_levi is not declared here.
  GradedLeviBound and the fusion total bound are not treated here.

Remarks:
* Integer-degree homogeneous slices avoid separate artificial support cutoffs at
  s = 0, t = 0 and v = 0. gtMixedSlice_nat_sub translates to the original natural
  degree recurrence only at the final evaluation step.
* The local scalar calculation works on every output row, so leading-monomial
  independence is unnecessary for this coefficient assembly. Finite free-module
  equality and e-Pieri give the evaluation equality directly.
* Multiplication need not have no zero divisors: infer each factor is nonzero from
  a nonzero product, without invoking mul_ne_zero_iff in a general commutative ring.
* Specify the coefficient ring explicitly when mapping PochhammerUnits into nested
  power series; otherwise elaboration can exhaust the default heartbeat limit.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    GTMixedFiveShift q h u := gtMixedFive_shift q h u

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    gtMixedFiveCoeff q h u = gtMixedFiveKernelCoeff q h u := gtMixed_five q h u

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedWeight_subsets
#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_shift_card
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_shift
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveKernelCoeff_recurrence
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five_coeff
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_branching
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_last_zero_coeff
