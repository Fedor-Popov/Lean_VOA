import VOA.DeligneAudit.D4CharRound102Audit
import VOA.DeligneAudit.D4CharCauchyShift

/-!
# The two-variable Cauchy identity: declaration and axiom audit

This module imports `D4CharRound102Audit` (with its type-A collision checks) together with
the results below.

Axiom check: of the audited theorems, 36 depend exactly on
`[propext, Classical.choice, Quot.sound]` and five elementary helpers on `[propext, Quot.sound]`.
All main results have the full standard axiom list. No `sorry` is used.

Proved, in namespace VOA.DeligneAudit.D4Char:
* `gtCauchyHead_tail`: X and B cancel every nonzero output tail, of arbitrary length.
  All row entries are integers; non-interlaced and negative boundary cases are included.
* `gtCauchySeed_subsets`: the entire local coefficient comparison in the exact subset
  and pieriCoeff notation. It holds on every integer row without a dominance hypothesis.
* `gtCauchyWeight_subsets`: the same identity with the normalization of gtCauchyTwoCoeff.
* `gtCauchyWeight_support`, `gtCauchyWeight_degree`, `gtCauchyWeight_dominant`,
  `gtCauchyWeight_shape`: complete finite support and degree bounds. These justify
  discarding negative source degrees and applying e-Pieri to every nonzero source.
* `gtCauchySlice_eval`: evaluation of the homogeneous free-module slice is precisely
  the definition gtCauchyTwoCoeff, with no altered sum or support condition.
* `gtPieriUp_apply`, `gtPieriUp_eval_card`: finite reindexing of the raising operator
  and its agreement with the proved e-Pieri theorem on dominant source rows.
* `gtCauchyTwoCoeff_recurrence`: the Euler-denominator coefficient recurrence in every
  bidegree, with no bound on either degree or on the highest weights.
* `gtCauchyTwo_shift`: GTCauchyTwoShift q h u N, for every N, using the actual
  gtCauchyTwoSeries of `D4CharRound102Audit`.
* `gtCauchy_two`: GTCauchyTwo q h u N, for every N, by the initial value and
  q-difference uniqueness. The ambient rank is N + 2.
* `gtCauchy_two_needed`: C(2,2), C(2,3), C(2,5) together, for all series degrees.

Not proved here:
* Lemma gP for m = 2. C(2,2) and C(2,3) are available through gtCauchy_two; the intended
  route expands the latter in the third variable by GT branching, compares it with C(2,2)
  times the one-row Euler series, and uses gtEval_formal_linearIndependent on the first two
  variables.
* The mixed-Cauchy instances with (m,n) at most (2,2), their down-step, Lemma O on
  D4K.ctTheta, specialization via D4K.jmap, and assembly with Ikernel_coeff_even
  are not proved in this chain. No m = 2 gP or mixed-Cauchy theorem is claimed here.
* HilbertIdentity is not proved; d4_hilbInt_eq_levi is not declared here.
* GradedLeviBound and the fusion total bound are not treated here. L3 and the
  unconditional Demazure rank theorem are available through `D4CharRound102Audit`.

Remarks:
* The tail calculation is uniform in rank and shorter than enumerating subsets separately
  at ranks 2, 3, 5.
* The coefficient identity is proved in the free module of integer rows, then evaluated
  at the GT polynomials. Thus linear independence is unnecessary for this sufficiency
  direction; it is necessary for the proposed gP coefficient extraction.
* The incoming tail state is essential: after an unselected zero the next selected
  box has factor 1 - q^0; at the first selected tail box the rank-two B identity applies.
* Reciprocal Pochhammer support proves the source row is dominant and its total degree
  is at least r. No finite highest-weight or degree checks replace these arguments.
* The actual q parameter need not be a unit: all results hold over any commutative
  ring with PochhammerUnits q, including the formal power-series coefficient ring.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q)
    (u : ℕ → Rˣ) (N : ℕ) : GTCauchyTwoShift q h u N := gtCauchyTwo_shift q h u N

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    GTCauchyTwo q h u 0 ∧ GTCauchyTwo q h u 1 ∧ GTCauchyTwo q h u 3 :=
  gtCauchy_two_needed q h u

example (u : ℕ → (PowerSeries ℤ)ˣ) (N : ℕ) :
    GTCauchyTwo PowerSeries.X (powerSeries_pochhammerUnits ℤ) u N :=
  gtCauchy_two PowerSeries.X (powerSeries_pochhammerUnits ℤ) u N

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtCauchySeed_subsets
#print axioms VOA.DeligneAudit.D4Char.gtCauchyWeight_subsets
#print axioms VOA.DeligneAudit.D4Char.gtCauchySlice_eval
#print axioms VOA.DeligneAudit.D4Char.gtPieriUp_eval_card
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwoCoeff_recurrence
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwo_shift
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two_needed
