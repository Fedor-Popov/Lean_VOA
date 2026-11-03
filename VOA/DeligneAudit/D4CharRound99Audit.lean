import VOA.DeligneAudit.D4CharPieriDominance
import VOA.DeligneAudit.D4LeviKSDemazureRank
import VOA.DeligneAudit.D4FiniteStatementProof
import VOA.DeligneAudit.DeligneFusionGrFilt
import VOA.DeligneAudit.DeligneFusionD1TensorGGrD4Model

/-!
# The realization-identity layers: combined import audit

Proved, layer (a):
* `gl4Hilb`, `qmultiCoeff`, and `d4LeviHilb` are exactly the RI convolution definitions.
* `HilbertIdentity` states L4, including the cast from natural to integer coefficients.
* `GradedLeviBound` states L1 for every Sat module.
* `leviTotalCount`, `d4LeviHilb_sum`, and `d4LeviHilb_tsum` prove L3 for every n.
  The finite-support statement is available for the squeeze.

Proved, layer (b):
* `gtP` is a genuine Laurent polynomial over integral polynomials in q, for integer weights.
  `gtEval` is its GT formula with variables specialized to units in any commutative ring.
* GT rank-zero/rank-one formulas, dominant interlacing rows, zero and determinant weights.
* Lemma 3.2(b), `gtEval_duality`, and 3.2(c), `gtP_central_shift`.
* Gaussian symmetry and balance, valid over arbitrary commutative rings.
* The all-length two-state transfer engine `pieri_transfer_chain` and its Gaussian instance.
* `EPieri` states Lemma E. Its r = 0, r = N, r > N cases and rank-one base hold.
* `pieriCoeff_zero_of_not_dominant` proves the vanishing needed by referee repair R2.

## Not proved here
* `EPieri` for general rank and interior r is not proved in this module (it is proved as
  `ePieri` in `D4CharEPieri`).
* Lemma 3.2(a) leading monomial/independence, 3.2(d) normalized Q branching, and the bridge
  from `gtEval` at four unit variables to `gl4Poly`.
* No proof of `HilbertIdentity` or `GradedLeviBound` is claimed. In particular there is no
  theorem `d4_hilbInt_eq_levi` here. Cauchy, mixed Cauchy, theta orthogonality, the D4
  specialization/squeeze, and the fusion total bound are not treated here.

Axiom check: the transfer arithmetic needs only propext and Quot.sound; the main count, GT,
and Gaussian theorems use exactly propext, Classical.choice, and Quot.sound. This module checks
coexistence with the finished rank chain (including both type-A chains), the finite kernel
proof, and the model/squeeze interfaces.
-/

namespace VOA.DeligneAudit.D4Char

example : LeviTotalCount := leviTotalCount

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.d4LeviHilb_sum
#print axioms VOA.DeligneAudit.D4Char.d4LeviHilb_tsum
#print axioms VOA.DeligneAudit.D4Char.gtP_central_shift
#print axioms VOA.DeligneAudit.D4Char.gtEval_duality
#print axioms VOA.DeligneAudit.D4Char.gaussian_pieri_transfer_chain
#print axioms VOA.DeligneAudit.D4Char.pieriCoeff_zero_of_not_dominant
