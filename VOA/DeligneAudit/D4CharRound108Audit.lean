import VOA.DeligneAudit.D4CharRound107Audit
import VOA.DeligneAudit.D4CharGradedFiltration

/-!
# L4 and the first degree-preserving layer of L1: declaration and axiom audit

Axiom check: every main theorem depends exactly on `[propext, Classical.choice, Quot.sound]`;
the word-degree helper uses `[propext, Quot.sound]`. No prohibited proof escape is used.
This module imports `D4CharRound107Audit`.

Proved, in namespace VOA.DeligneAudit.D4Char:
* KernelDiagonal and KernelProduct transport the diagonal numerator and all hyper
  factors through the homogeneous substitution. These are formal series identities.
* KernelIdentification proves rsMixedKernel_eq_kernelM, retaining the extra scalar
  EPos 1 0 2 two_ne_zero. The four numerator factors reduce to that factor times
  the original three kernel numerator factors; all sixteen hyper factors match.
* DemazureConvolution applies the Euler inverse and the theorem
  D4K.Ikernel_coeff_even D4Finite.d4FiniteIdentity_holds. This identifies each
  even kernel moment with (qpoch n)^-1 times the original D4K.Cdem n.
* DemazureCharacter proves rsCdem_eq_gt_sum for every n: the full four-index
  q-multinomial sum of GL_4 mixed GT polynomials. No degree range is truncated.
* GTHilbert identifies evaluation of GL_2, GL_3, and GL_4 GT polynomials at the
  unit alphabet with the gl2Poly, gl3Poly, and gl4Poly definitions.
* HilbertSpecialization proves rsEvOne_Cdem, the equality of ev1(Cdem n) with
  the image of d4LeviPoly n in D4K.Kq. The explicit rational polynomial map
  preserves the original q-to-q^2 convention and coefficients in all degrees.
* HilbertIdentity proves d4_hilbInt_eq_levi for every n,N, including zero, by
  ev1_Cdem and coefficient comparison. d4_hilbertIdentity proves the
  HilbertIdentity proposition. L4 holds with no hypotheses.
* GradedReduction proves finite dimensionality of each cycDeg, and
  gradedLeviBound_iff_universal reduces L1 to the universal presented modules.
  d4_cycDeg_le_total is only the inherited coarse bound by 29^n.
* GradedKeys keeps the radical seed's wordKey.degree in gradedKeyOrbit. It proves
  degree projection of keyOrbit, its equality with the degree intersection in
  the universal module, and d4_universal_degree_eq_keys for the full finite key box.
  Keys of degree greater than N have zero exact-degree orbit.
* GradedFiltration proves degree projection preserves every key prefix, and the
  next prefix is the preceding one plus the explicit graded key orbit in the
  universal module. d4_degree_finrank_eq_steps is an exact dimension telescoping
  formula for every Sat module, n, and N, with finite graded step quotients.

## Not proved here
* L1 is not proved in this module. The graded filtration and quotient-rank formula
  reduce it to graded Levi orbit bounds and degreewise key counts: sharp graded type-A
  estimates for the relevant GL_4/GL_3/GL_2 quotients (retaining the radical seed degree
  and the quotient by earlier keys), with degreewise sum bounded by the q-multinomial
  formula d4LeviHilb, transferred to all Sat modules by gradedLeviBound_iff_universal.
  (L1 is proved in `D4CharRound109Audit`.)
* The general Demazure realization hD, the final squeeze and the fusion total bound hF
  are not claimed here.

## Remarks
* Do not drop the extra EPos factor: its inverse supplies the fourth convolution
  index in rsCdem_eq_gt_sum. The original three-index moment formula is not Cdem.
* rsPolyMap is a rational-polynomial version of the coefficient embedding;
  its coefficient theorem reads at 2*N. The final integer equality uses exact casts.
* Degree projection and gradedKeyPrefix_univ_step are proved on the universal
  module. An arbitrary Sat module need not have a direct grading. Use the universal
  reduction instead of assuming projection descends to every Sat quotient.
-/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 DeligneCharacter

example (n N : ℕ) : D4K.hilbInt n N = (d4LeviHilb n N : ℤ) :=
  d4_hilbInt_eq_levi n N

example : HilbertIdentity := d4_hilbertIdentity

example : GradedLeviBound ↔ UniversalGradedLeviBound := gradedLeviBound_iff_universal

example (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := d4LeviHilb_tsum n

example : UnivG.DemazureUnivRank := D4Levi.d4_demazureUnivRank

example (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (h : Sat D4sector.f ρ w (ravFam D4sector n 0)) (N : ℕ) :
    Module.finrank ℂ (cycDeg ρ w N) =
      ∑ i ∈ Finset.range (D4Levi.globalKeyBox n).card,
        Module.finrank ℂ (LeviKeyFiltration.StepQuot (gradedKeyPrefix ρ w n N) i) :=
  d4_degree_finrank_eq_steps n ρ w h N

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtFourDiagonal_product
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_eq_kernelM
#print axioms VOA.DeligneAudit.D4Char.rsKernel_moment_demazure
#print axioms VOA.DeligneAudit.D4Char.rsCdem_eq_gt_sum
#print axioms VOA.DeligneAudit.D4Char.rsGT_gl4Poly
#print axioms VOA.DeligneAudit.D4Char.rsEvOne_Cdem
#print axioms VOA.DeligneAudit.D4Char.d4_hilbInt_eq_levi
#print axioms VOA.DeligneAudit.D4Char.d4_hilbertIdentity
#print axioms VOA.DeligneAudit.D4Char.gradedLeviBound_iff_universal
#print axioms VOA.DeligneAudit.D4Char.d4_universal_degree_eq_keys
#print axioms VOA.DeligneAudit.D4Char.gradedKeyPrefix_univ_step
#print axioms VOA.DeligneAudit.D4Char.d4_degree_finrank_eq_steps
