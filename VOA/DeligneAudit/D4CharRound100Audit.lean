import VOA.DeligneAudit.D4CharRound99Audit
import VOA.DeligneAudit.D4CharEPieri

/-!
# General e-Pieri: declaration audit and combined imports

This module imports the e-Pieri chain together with the earlier `D4Char` modules.

Proved, uniformly in rank, highest weight, and elementary degree:
* `intQbinom_pascal`, `intQbinom_balance`, `intQbinom_lower`: zero-extended integer Gaussian
  identities, including b = -1, a = 0, and both out-of-range tails.
* `pieriW_entries`: the four genuine integer Gaussian entries in Lemma E.
* `pieri_transfer_binary`, `pieri_e_step`: the two transfer runs as complete finite sums
  over Boolean states, followed by the exact E-step.
* `gtPsiZero_of_not_mem`, `gtEval_sum_box`, `gtPsiZero_raise_sum`: the zero extension and
  a common finite interlacing box, with a proved reindexing for each binary raising.
* `pieri_e_step_rows`, `pieri_branch_intertwine`: GT coefficient comparison, including
  boundary terms, before the induction on rank.
* `gtEval_pieri_generating`: the full GT induction, initially for a unit parameter q.
* `ePieri_unit`: extraction of every elementary degree, matching the original `EPieri` API.
* `ePieri_polynomial`, `ePieri`: the unit hypothesis is removed by the injective map from
  polynomials to Laurent polynomials followed by polynomial evaluation. Thus `ePieri` has
  no additional hypothesis on q or the coefficient ring.
* `gtP_ePieri`: Lemma E for the Laurent polynomials `gtP`.

## Not proved here
* Lemma 3.2(a) (leading monomial one, dominance triangularity, and linear independence).
* Normalized Q-branching, Lemma 5.1, identities X/B/Y, ordinary Cauchy and gP, the needed
  mixed-Cauchy instances, theta orthogonality, and D4 specialization/assembly.
* `HilbertIdentity` (L4); `d4_hilbInt_eq_levi` is not declared.
* The graded Levi bound (L1) and the fusion total bound. L3 and the unconditional Demazure
  rank theorem are available through the import of `D4CharRound99Audit`.

## Remarks
* `gtPsi` alone is not a zero extension: its `Int.toNat` lower index turns a negative
  integer into zero. Use `gtPsiZero` for extended summation boxes and its membership lemmas.
* The generic `gtEval_map`, `pieriCoeff_map`, `pieriElementary_map`, and `pieriRHS_map` are
  available for specialization into other coefficient rings.
* `pieriRowCoeff` uses integer powers and Boolean subsets; `pieriRowCoeff_indicator`
  identifies it with the original `pieriCoeff` on dominant rows.
* All variables remain units, as required by integer highest weights. The parameter q in
  the final theorem is an arbitrary ring element, including zero and zero divisors.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ) : EPieri q u := ePieri q u

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.intQbinom_pascal
#print axioms VOA.DeligneAudit.D4Char.intQbinom_balance
#print axioms VOA.DeligneAudit.D4Char.intQbinom_lower
#print axioms VOA.DeligneAudit.D4Char.pieri_e_step
#print axioms VOA.DeligneAudit.D4Char.pieri_e_step_rows
#print axioms VOA.DeligneAudit.D4Char.pieri_branch_intertwine
#print axioms VOA.DeligneAudit.D4Char.gtEval_pieri_generating
#print axioms VOA.DeligneAudit.D4Char.ePieri_unit
#print axioms VOA.DeligneAudit.D4Char.ePieri_polynomial
#print axioms VOA.DeligneAudit.D4Char.ePieri
#print axioms VOA.DeligneAudit.D4Char.gtP_ePieri
