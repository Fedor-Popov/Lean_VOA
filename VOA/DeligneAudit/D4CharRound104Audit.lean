import VOA.DeligneAudit.D4CharRound103Audit
import VOA.DeligneAudit.D4CharMixedFiveUnique

/-!
# Rank-two gP and the stable mixed-Cauchy local equation: declaration and axiom audit

This module imports `D4CharRound103Audit` (with the type-A collision checks) together with
the results below.

Axiom check: every audited theorem depends exactly on `[propext, Classical.choice, Quot.sound]`.
No `sorry` is used.

Proved, in namespace VOA.DeligneAudit.D4Char:
* GPTwoCoeff: `gtQ_two_oneRow`, `gtGP_two_normalized` reduce rank-two gP to C(2,2).
* GPTwo: `gtGP_two`, `gtGP_two_branching` prove Lemma gP for every partition (c,d)
  and every k. `sum_gtGPUppersTwo` proves that the parametrized sum includes every
  interlacing upper partition exactly once, with total-size increment k.
* MixedSeparator: `gtMixed_one_head`, `gtMixed_two_bits` prove the X/B separator
  calculation with an arbitrary negative-block continuation, including all bad
  middle entries. The continuation is not restricted to a zero tail.
* MixedLocal: `gtMixedSeed_subsets` expresses this calculation in exact e-Pieri
  subset notation, on every integer output row and any remaining tail length.
  `gtMixedSeed_bad_middle` kills every nonzero middle entry.
* MixedNegative: `gtQ_two_eOne`, `gtQ_two_eTwo`, `gtMixedTailAction_Q_two` prove the
  two-row negative-block Y calculation. The equal-part/nondominant boundary is
  included. No division by a zero gap is used.
* MixedFiveLocal: `gtMixedFive_good_normalized` is the local X times Y comparison
  at GL_5 with `gtNegativeQTwo`, the actual zero-extended negative-partition function.
* MixedFiveDominant: `gtMixedFive_local_normalized` is the complete local equation
  for every dominant GL_5 output row, including all the bad-middle cases.
* MixedKernel: `gtMixedEulerStep_shift` proves the mixed Euler-kernel shift, retaining
  the two y-side factors. `gtMixedEulerStep_unique` is its q-difference reduction.
* MixedFiveCoeff: `gtMixedFiveCoeff` is the finite four-degree GT sum for MC_(2,2,5).
  `gtMixedFiveCoeff_zero_x` proves its negative-only C(2,5) base by GT duality;
  `gtMixedFiveCoeff_zero_y` proves the positive-only boundary. Both x and y swaps hold.
* MixedFiveUnique: `gtMixedFiveRecurrence_unique` proves uniqueness of the four-degree
  recurrence from x symmetry and the negative-only base. Thus the same recurrence
  handles both positive-variable induction steps. `gtMixedFiveCoeff_eq_of_shift`
  is conditional on GTMixedFiveShift and the comparison array's recurrence,
  symmetry and boundary; it is not an unconditional mixed-Cauchy theorem.

Not proved here:
* `GTMixedFiveShift q h u` is defined but not proved in this module. It is the homogeneous
  equation F(qz)(1-z y_1)(1-z y_2) = F(z) prod_i(1-z u_i), stated in all four natural
  degrees. Its proof needs finite homogeneous support/reindexing: apply e-Pieri to the
  u-side, then use `gtMixedFive_local_normalized` and extract the two negative Q degrees.
  The local theorem itself does not perform this homogeneous assembly.
* The stable MC_(2,2,5) assembly: express the four-variable Euler kernel as the comparison
  array G, derive its recurrence from `gtMixedEulerStep_shift`, then use
  `gtMixedFiveCoeff_eq_of_shift`. No full mixed-Cauchy instance is claimed here, and no
  hshift hypothesis is discharged here.
* The N = 5 to N = 4 constant-term down-step needs its GT branching regrouping
  and cancellation of Gamma. Both uses of rank-two gP are available.
* Lemma O on D4K.ctTheta, specialization via D4K.jmap, and assembly with
  Ikernel_coeff_even and ev1_Cdem are not proved in this chain.
* HilbertIdentity is open; d4_hilbInt_eq_levi is not declared here.
  GradedLeviBound and the fusion total bound are not treated here.

Remarks:
* A short gP proof: Q_(c,d) is 1/(q)_d times the determinant shift of the one-row
  Q_(c-d). C(2,2) expands its product with g_k; Gaussian normalization identifies the
  coefficients with psi_(kappa,0)/(c,d). Hence C(2,3) coefficient extraction and
  leading-monomial independence are unnecessary for rank-two gP.
* Integer row coordinates must be cast explicitly from natural arithmetic when
  matching gtCauchyTwoCoeff. In particular, the first parts of gtMixedFiveCoeff are
  (r+s-b : Nat) and (t+v-d : Nat), then cast to integers.
* The q parameter need not be a unit. All theorems here hold over arbitrary commutative
  rings with PochhammerUnits q, including integral formal q-series.
* The local mixed equation is stronger than a finite degree check but weaker than
  the completed formal-series shift.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d k : ℕ) (hd : d ≤ c) :
    (∑ p ∈ gtGPUppersTwo c d k,
      gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c : ℤ), (d : ℤ)] *
        gtQ q h u 2 ![(p.1 : ℤ), (p.2 : ℤ)]) =
      gtOneRowCoeff q h u 2 k * gtQ q h u 2 ![(c : ℤ), (d : ℤ)] :=
  gtGP_two_branching q h u c d k hd

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtGP_two_branching
#print axioms VOA.DeligneAudit.D4Char.gtMixedSeed_subsets
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_local_normalized
#print axioms VOA.DeligneAudit.D4Char.gtMixedEulerStep_shift
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_zero_x
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRecurrence_unique
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_eq_of_shift
