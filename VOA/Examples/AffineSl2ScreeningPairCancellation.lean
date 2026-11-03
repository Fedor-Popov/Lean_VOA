/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningWeightedEuler
import VOA.Examples.VirasoroScreeningPairSums

/-!
# Exact pairwise screening cancellation after coefficient extraction

The weighted Vandermonde derivative is an actual polynomial identity.
Combining it with finite integration by parts and endpoint counting leaves
only the scalar term in the screening lowering equation.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Restoring either deleted beta factor gives the opposite single omission. -/
theorem pairOmittedIntegrand_restore (r q M : ℕ) (i j : Fin r) (hij : i≠j) :
    betaFactor r (r*(q-1)) j*pairOmittedIntegrand r q M i j=
      omittedIntegrand r q M i := by
  have h := betaOmitPair_restore r (r*(q-1)) i j hij
  unfold betaOmitPair betaOmit at h
  rw [pairOmittedIntegrand,omittedIntegrand]
  rw [show betaFactor r (r*(q-1)) j*(delta r^(2*M)*
    (∏ l∈(Finset.univ.erase i).erase j,betaFactor r (r*(q-1)) l)*
    ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1))=
    delta r^(2*M)*(betaFactor r (r*(q-1)) j*
    (∏ l∈(Finset.univ.erase i).erase j,betaFactor r (r*(q-1)) l))*
    ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1) by ring,h]

/-- The actual weighted Vandermonde contribution is the finite unordered
companion sum, with its exact factor 2M and no inverse differences. -/
theorem vandermonde_omission_sum (r q M : ℕ) :
    (∑ i : Fin r,auxiliaryEuler i (delta r^(2*M))*
      ((∏ j∈Finset.univ.erase i,betaFactor r (r*(q-1)) j)*
        ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)))=
    (2*M : ℂ) • (∑ ij∈variablePairs r,
      betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2) := by
  have h := congrArg (fun P : Auxiliary r => P*
    ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1))
    (weightedEuler_delta_power r (r*(q-1)) M)
  dsimp only at h
  rw [weightedEuler_apply,Finset.sum_mul,smul_mul_assoc,
    Finset.mul_sum,Finset.sum_mul] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro i hi
    dsimp only [betaOmit]
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    dsimp only [betaOmitPair,pairOmittedIntegrand]
    ring

/-- The exact selected-coefficient form of weighted Vandermonde differentiation. -/
theorem selected_vandermonde_omission_sum (r q M : ℕ) :
    (∑ i : Fin r,(auxiliaryEuler i (delta r^(2*M))*
      ((∏ j∈Finset.univ.erase i,betaFactor r (r*(q-1)) j)*
        ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)))=
    (2*M : ℂ) • (∑ ij∈variablePairs r,
      (betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  have h := congrArg (fun P : Auxiliary r => P
    (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) (vandermonde_omission_sum r q M)
  dsimp only at h
  rw [auxiliary_sum_apply] at h
  change _=(2*M : ℂ) • ((∑ ij∈variablePairs r,
      betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2) _) at h
  rw [auxiliary_sum_apply] at h
  exact h

/-- Summing finite omitted-factor integration by parts gives the companion
pair sum, retaining the factor M rather than assuming it invertible. -/
theorem summed_omitted_ibp (r q M : ℕ) (hq : 0<q) :
    (M : ℂ) • (∑ i : Fin r,
      (bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)))=
    (2*M : ℂ) • (∑ ij∈variablePairs r,
      (betaCompanion r (r*(q-1)) ij.1 ij.2*pairOmittedIntegrand r q M ij.1 ij.2)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) -
    (((r-1)*M+q-1 : ℕ) : ℂ) • (∑ i : Fin r,
      omittedIntegrand r q M i (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  rw [Finset.smul_sum]
  simp_rw [omittedIntegrand_ibp r q M hq]
  rw [Finset.sum_sub_distrib,← Finset.smul_sum,selected_vandermonde_omission_sum]

/-- Pair endpoint counting cancels the divided differences exactly as
polynomials, before any extraction or scalar division. -/
theorem pair_divided_companion_sum (r q M : ℕ) :
    (∑ ij∈variablePairs r,
      ((betaDivided r (r*(q-1)) ij.1 ij.2+betaCompanion r (r*(q-1)) ij.1 ij.2)*
        pairOmittedIntegrand r q M ij.1 ij.2))=
      (r-1) • (∑ i : Fin r,omittedIntegrand r q M i) := by
  calc
    _ = ∑ ij∈variablePairs r,(omittedIntegrand r q M ij.1+
        omittedIntegrand r q M ij.2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hne := ne_of_lt (Finset.mem_filter.mp hij).2
      rw [betaDivided_add_companion,add_mul,
        pairOmittedIntegrand_restore r q M ij.1 ij.2 hne,
        pairOmittedIntegrand_swap r q M ij.1 ij.2,
        pairOmittedIntegrand_restore r q M ij.2 ij.1 (Ne.symm hne)]
      exact add_comm _ _
    _ = _ := screening_pair_sum r _

end
end VOA.Wak.Screening
