/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningBetaOmission

/-!
# Actual second beta partials and ordered pairs of omitted factors

A beta factor is linear in every oscillator. Two beta partials therefore
remove distinct factors. The formulas retain ordered pairs, so no factor
of two or unordered-pair convention is silently introduced.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The actual integrand with two beta factors erased. Later sums use
i and j distinct; this definition itself makes sense for every pair. -/
def pairOmittedIntegrand (r q M : ℕ) (i j : Fin r) : Auxiliary r :=
  delta r^(2*M)*(∏ l∈(Finset.univ.erase i).erase j,betaFactor r (r*(q-1)) l)*
    ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)

/-- The derivative of an omitted integrand removes a second, distinct
beta factor and inserts the corresponding auxiliary monomial. -/
theorem omittedIntegrand_beta_partial (r q M d : ℕ) (hd : d≤r*(q-1)) (i : Fin r) :
    oscillatorPartial r (0,d) (omittedIntegrand r q M i)=
      ∑ j∈Finset.univ.erase i,(single ((d : ℤ) • unitExponent r j) 1 : Auxiliary r)*
        pairOmittedIntegrand r q M i j := by
  have he := derivative_prod_zero (oscillatorPartial r (0,d))
    (Finset.range (r*(q-1))) (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => oscillatorPartial_exponentialFactor_beta r _ M _ d)
  rw [omittedIntegrand,(oscillatorPartial r (0,d)).leibniz,he,
    (oscillatorPartial r (0,d)).leibniz,
    (oscillatorPartial r (0,d)).leibniz_pow,oscillatorPartial_delta,
    derivative_prod_omissions]
  simp only [smul_zero,add_zero,smul_eq_mul,mul_zero,zero_add,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [oscillatorPartial_betaFactor,if_pos hd,pairOmittedIntegrand]
  ring

/-- The actual second beta derivative of the full integrand is an ordered
sum over distinct omitted factors, with both auxiliary monomial insertions. -/
theorem integrand_beta_double_partial (r q M a b : ℕ)
    (ha : a≤r*(q-1)) (hb : b≤r*(q-1)) :
    oscillatorPartial r (0,b) (oscillatorPartial r (0,a) (integrand r q M))=
      ∑ i : Fin r,∑ j∈Finset.univ.erase i,
        (single ((a : ℤ) • unitExponent r i) 1 : Auxiliary r)*
        (single ((b : ℤ) • unitExponent r j) 1 : Auxiliary r)*
          pairOmittedIntegrand r q M i j := by
  rw [integrand_beta_partial_omissions r q M a ha,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(oscillatorPartial r (0,b)).leibniz,oscillatorPartial_single,pderiv_one,
    AddMonoidAlgebra.single_zero,smul_zero,add_zero,
    omittedIntegrand_beta_partial r q M b hb i]
  simp only [smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- The actual two oscillator partials of the screening vector equal the
selected finite ordered-pair expression. The diagonal pair i=j is absent
because each individual beta factor is oscillator-linear. -/
theorem state_beta_double_partial (r q M a b : ℕ)
    (ha : a≤r*(q-1)) (hb : b≤r*(q-1)) :
    pderiv (0,b) (pderiv (0,a) (state r q M))=
      ∑ i : Fin r,∑ j∈Finset.univ.erase i,
        ((single ((a : ℤ) • unitExponent r i) 1 : Auxiliary r)*
        (single ((b : ℤ) • unitExponent r j) 1 : Auxiliary r)*
          pairOmittedIntegrand r q M i j)
          (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  rw [state,← oscillatorPartial_apply,← oscillatorPartial_apply,
    integrand_beta_double_partial r q M a b ha hb,auxiliary_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [auxiliary_sum_apply]

/-- The first and second deleted factors can be exchanged without changing
the remaining actual integrand. Ordered-pair counting can therefore be
converted to unordered pairs later using an explicit combinatorial proof. -/
theorem pairOmittedIntegrand_swap (r q M : ℕ) (i j : Fin r) :
    pairOmittedIntegrand r q M i j=pairOmittedIntegrand r q M j i := by
  have h : (Finset.univ.erase i).erase j=(Finset.univ.erase j).erase i := by
    ext l
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    exact and_comm
  rw [pairOmittedIntegrand,pairOmittedIntegrand,h]

end
end VOA.Wak.Screening
