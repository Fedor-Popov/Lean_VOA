import VOA.DeligneAudit.D4CharRound100Audit
import VOA.DeligneAudit.D4CharQDifference

/-!
# GT independence, Q branching, and q-difference uniqueness: declaration and axiom audit

This module imports both type-A chains (through `D4CharRound100Audit`) together with the
results below.

Axiom check: every audited theorem depends exactly on `[propext, Classical.choice, Quot.sound]`.
No `sorry` is used.

Completed, uniformly in rank and integer highest weight:
* `gtPoly_eq_gtEval`, `gtPoly_X_eq_gtP`: a monomial-coordinate form of the existing GT
  recursion, with an explicit bridge back to the original polynomials.
* `gtPoly_support_bounds`, `gtP_support_bounds`: no variables beyond rank N, the correct
  total exponent, and every initial partial sum bounded by the corresponding highest sum.
* `gtPoly_leading_coeff`, `gtP_leading_coeff`: coefficient one at the highest weight.
* `gtPoly_linearIndependent`, `gtP_linearIndependent`, `gtEval_formal_linearIndependent`:
  Lemma 3.2(a). The generic version allows any commutative ring and any q, including zero
  divisors. A maximal sum of partial sums in a finite relation detects a nonzero coefficient.
* `powerSeries_pochhammerUnits`: all Pochhammer products are units over A[[q]], for any A.
* `gtQ_branching`, `gtQBranch_product`: Lemma 3.2(d), including its numerator Pochhammer
  factors and the last-part denominator. No field of fractions is introduced.
* `gtQBranch_degree_zero`: equal total sizes force deletion of a final zero, with coefficient 1.
* `gtQCoeff_eq_ite`, `gtQ_branching_product`: the complete integer zero extension, including
  both failed interlacing inequalities and a negative last part, even in rank one.
* `qDifference_coeff_rec`, `qDifference_unique`, `qDifference_zero`: Lemma 5.1, directly in
  PowerSeries over any commutative ring in which each 1 - q^n, n > 0, is a unit.
* `qDifference_unique_of_series_map`: the integral formal-series version after any coefficient
  ring homomorphism. This covers the Laurent and further formal-series coefficient rings
  used in Cauchy, since ring homomorphisms preserve the required units.

Not proved here:
* Lemmas 3.2(a), 3.2(d), and 5.1 are proved; Lemma E is available from `D4CharRound100Audit`.
* The identities X and B (including the non-interlaced cancellation) and Y with both
  partitions are not proved here. `gtQCoeff` is the zero-extended c coefficient intended for
  them.
* C(m,N) and gP are not stated or proved here. The one-row/Euler generating-series bridge
  of Lemma 3.2(e) is not supplied here. The mixed-Cauchy instances, theta orthogonality
  (Lemma O), specialization through jmap, and kernel assembly are open.
* `HilbertIdentity` (L4) is not proved; `d4_hilbInt_eq_levi` is not declared.
  The `gtEval` to `gl4Poly` specialization bridge is also not proved here.
* `GradedLeviBound` (L1) and the fusion total bound are not treated here. L3 and the
  unconditional Demazure rank theorem are available through the combined imports.

Conventions and implementation notes:
* `gtQ` extends the normalized expression to integer rows using naturalized gaps. Its
  branching-product theorem requires a nonnegative last part. For unrestricted rows use
  `gtQCoeff`, which explicitly vanishes outside the partition/interlacing region.
* `gtQBranch` alone is not zero extended; neither is `gtPsi`. Do not replace `gtQCoeff`
  by either one when summing over enlarged boxes in X or B.
* A coefficient of AddMonoidAlgebra is accessed via `.coeff` when rewriting finite sums;
  this avoids accidental dependence on a Finsupp implementation simplification.
-/

namespace VOA.DeligneAudit.D4Char

example (N : ℕ) : LinearIndependent (Polynomial ℤ)
    (fun lam : {lam : Fin N → ℤ // Antitone lam} => gtP N lam.val) :=
  gtP_linearIndependent N

example : PochhammerUnits (PowerSeries.X : PowerSeries ℤ) :=
  powerSeries_pochhammerUnits ℤ

example (A B G H : PowerSeries (PowerSeries ℤ))
    (hA : PowerSeries.constantCoeff A = 1) (hB : PowerSeries.constantCoeff B = 1)
    (hG : PowerSeries.rescale PowerSeries.X G * A = G * B)
    (hH : PowerSeries.rescale PowerSeries.X H * A = H * B)
    (hzero : PowerSeries.constantCoeff G = PowerSeries.constantCoeff H) : G = H :=
  qDifference_unique PowerSeries.X (powerSeries_qDifferenceUnits ℤ) A B G H hA hB hG hH hzero

example {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ) : EPieri q u := ePieri q u

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtP_support_bounds
#print axioms VOA.DeligneAudit.D4Char.gtP_leading_coeff
#print axioms VOA.DeligneAudit.D4Char.gtP_linearIndependent
#print axioms VOA.DeligneAudit.D4Char.gtEval_formal_linearIndependent
#print axioms VOA.DeligneAudit.D4Char.gtQ_branching
#print axioms VOA.DeligneAudit.D4Char.gtQBranch_product
#print axioms VOA.DeligneAudit.D4Char.gtQBranch_degree_zero
#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_eq_ite
#print axioms VOA.DeligneAudit.D4Char.gtQ_branching_product
#print axioms VOA.DeligneAudit.D4Char.qDifference_coeff_rec
#print axioms VOA.DeligneAudit.D4Char.qDifference_unique
#print axioms VOA.DeligneAudit.D4Char.qDifference_unique_of_series_map
