import VOA.DeligneAudit.D4CharRound101Audit
import VOA.DeligneAudit.D4CharCauchyTwo

/-!
# X, B, Y, Euler and ordinary Cauchy in one variable: declaration and axiom audit

This module combines the chain below with `D4CharRound101Audit` and its type-A collision checks.

Axiom check: 48 of the printed theorems depend exactly on `[propext, Classical.choice,
Quot.sound]`, and three elementary helpers use only `[propext, Quot.sound]`.

Proved:
* `gtInvPoch_lower`, `gtInvPoch_raise`: reciprocal Pochhammer recurrences on every
  integer, including zero and the entire negative half-line.
* `gtQ_two_state_zero`, `gtQ_two_state_one`: the two-state recursion for X and B,
  on arbitrary integer rows. In particular the non-interlaced gap -1 is included.
* `gtX_small_rank`, `gtB_small_rank`: X and B in the actual subset/Pieri notation
  for upper rows of length one or two. All row entries are unrestricted integers.
  These are exactly the alphabet ranks required by C(2,N) and MC with m at most two.
* `gtY`, `gtY_normalized`: identity Y in every rank, with both rows required to be
  partitions (referee repair R2). `gtQ_ePieri` is normalized e-Pieri with the
  exiting-edge coefficients, summed only over dominant raised rows.
* `gtEulerInv_shift`, `gtEulerPos_shift`, `gtEulerPos_mul_inv`: both Euler series,
  their q-difference equations, and their inverse relation over any commutative
  ring satisfying PochhammerUnits. No field of fractions is introduced.
* `gtEval_oneRow_branching`, `gtQ_oneRow_branching`: the one-row GT recursion and
  its normalized convolution, for every rank and every nonnegative row length.
* `gtCauchy_one`, `gtCauchy_one_GT`, `gtEulerInv_product_coeff`: C(1,N) and Lemma
  3.2(e), including zero variables and all degrees. `gtGP_one`: gP for m = 1.
* `gtQ_two_expansion`: the explicit two-variable Q formula, all nonnegative parts.
* `gtCauchyTwoCoeff`: the finite x^r y^s coefficient of the C(2,N+2) candidate.
  Its symmetry and both initial boundaries are proved. `gtCauchy_two_of_shift`
  proves C(2,N+2) *conditional on* the concrete target `GTCauchyTwoShift`.

## Not proved here
* `GTCauchyTwoShift q h u N` is not proved in this module. It asks for the last-variable
  shift of `gtCauchyTwoSeries`, whose coefficients are finite sums of the actual gtEval.
  The initial value and uniqueness step are complete in gtCauchy_two_of_shift.
  The required values are N = 0, 1, 3, corresponding to C(2,2), C(2,3), C(2,5).
  (It is proved as `gtCauchyTwo_shift` in `D4CharCauchyShift`.)
* gP for m = 2, which needs C(2,2), C(2,3) and leading-monomial independence.
* The mixed-Cauchy instances, their down-step, theta orthogonality, specialization
  via jmap, and assembly with Ikernel_coeff_even.
* `HilbertIdentity`; `d4_hilbInt_eq_levi` is not declared here, and no statement of the
  Demazure realization identity is claimed.
* GradedLeviBound and the fusion total bound. L3 and the unconditional Demazure rank
  theorem are available through `D4CharRound101Audit`.

## Remarks
* X and B are specialized only in alphabet rank, never in highest weight or degree.
  The integer reciprocal recurrence handles the bad interlacing region directly,
  without dividing by the potentially zero gap factor.
* Unqualified `C` and `mk` resolve to existing VOA declarations in this namespace.
  Series definitions use PowerSeries.C and PowerSeries.mk explicitly.
* In C(2,N+2), the coefficient with second part b is
  I(r-b) I(s-b) I(b) P_(r+s-b,b,0,...,0), with 0 <= b <= min(r,s).
  There is no extra q-power. The natural index N counts trailing zeroes.
-/

namespace VOA.DeligneAudit.D4Char

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q)
    (lam : Fin 2 → ℤ) (μ : Fin 1 → ℤ) :
    gtXSum q h lam μ = q ^ ((∑ i, lam i) - ∑ i, μ i).toNat * gtQCoeff q h lam μ :=
  gtX_rank_two q h lam μ

example {R : Type*} [CommRing R] (q : R) (h : PochhammerUnits q)
    (lam : Fin 2 → ℤ) (μ : Fin 1 → ℤ) : gtBSum q h lam μ = 0 :=
  gtB_rank_two q h lam μ

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtX_small_rank
#print axioms VOA.DeligneAudit.D4Char.gtB_small_rank
#print axioms VOA.DeligneAudit.D4Char.gtY
#print axioms VOA.DeligneAudit.D4Char.gtQ_ePieri
#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_mul_inv
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_one
#print axioms VOA.DeligneAudit.D4Char.gtGP_one
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_expansion
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two_of_shift
