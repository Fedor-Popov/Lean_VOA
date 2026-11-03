/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningPairCancellation

/-!
# Actual oscillator sums as selected finite screening expressions

The boson-beta sum inserts the finite boson series. The quadratic beta
sum inserts the finite divided difference. Total auxiliary degree proves
that second derivatives beyond the screening cutoff vanish.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Multiplication of a selected auxiliary coefficient by an oscillator
polynomial can be moved inside as a constant Laurent monomial. -/
theorem selected_constant_mul (r : ℕ) (P : WakFock) (Q : Auxiliary r) (g : Fin r→ℤ) :
    ((single 0 P : Auxiliary r)*Q) g=P*Q g :=
  AddMonoidAlgebra.single_zero_mul_apply _ _ _

/-- The actual finite boson-beta sum equals the extracted boson insertions
into the single-omission integrands. -/
theorem state_boson_sum_selected (r q M : ℕ) :
    (∑ j∈Finset.range (r*(q-1)),X (2,j)*pderiv (0,j+1) (state r q M))=
      ∑ i : Fin r,(bosonAuxiliarySeries r (r*(q-1)) i*omittedIntegrand r q M i)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  classical
  calc
    _ = ∑ j∈Finset.range (r*(q-1)),∑ i : Fin r,
      ((single (((j+1 : ℕ) : ℤ) • unitExponent r i) (X (2,j)) : Auxiliary r)*
        omittedIntegrand r q M i) (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [state_beta_partial_omissions r q M (j+1) (by have := Finset.mem_range.mp hj; omega),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← selected_constant_mul r (X (2,j)),← mul_assoc,single_mul_single]
      simp only [zero_add,mul_one]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [bosonAuxiliarySeries,Finset.sum_mul,auxiliary_sum_apply]

/-- Pair omissions have nonnegative auxiliary degree after removing the
Vandermonde; the same holds for the finite exponential. -/
theorem pairOmission_remainder_lower (r q M : ℕ) (i j : Fin r) :
    LowerDegree 0 ((∏ l∈(Finset.univ.erase i).erase j,betaFactor r (r*(q-1)) l)*
      ∏ m∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (m+1)) := by
  simpa using (lowerDegree_prod_zero _ _ (fun l _ => betaFactor_lower r _ l)).mul
    (lowerDegree_prod_zero _ _ (fun m _ => exponentialFactor_lower r _ M (m+1)))

/-- A pair insertion above the remaining total degree has zero selected
coefficient, even when both individual indices are below cutoff. -/
theorem selected_pair_above_degree (r q M a b : ℕ) (hq : 0<q)
    (hab : r*(q-1)<a+b) (i j : Fin r) :
    ((single ((a : ℤ) • unitExponent r i) 1 : Auxiliary r)*
      (single ((b : ℤ) • unitExponent r j) 1 : Auxiliary r)*
      pairOmittedIntegrand r q M i j)
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  let T : Auxiliary r := single ((a : ℤ) • unitExponent r i) 1*
    single ((b : ℤ) • unitExponent r j) 1
  have hT : LowerDegree ((a : ℤ)+b) T := by
    exact (LowerDegree.single r _ _ 1 (le_of_eq (exponentDegree_smul_unit r i a).symm)).mul
      (LowerDegree.single r _ _ 1 (le_of_eq (exponentDegree_smul_unit r j b).symm))
  have hbound : (r : ℤ)*(q-1)+1≤(a : ℤ)+b := by
    have hq' : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
    have hab' : (r : ℤ)*((q-1 : ℕ) : ℤ)<(a : ℤ)+b := by exact_mod_cast hab
    rw [hq'] at hab'
    omega
  have hz := screening_high_degree_product_zero r q M hq T _ (hT.mono hbound)
    (pairOmission_remainder_lower r q M i j)
  convert hz using 1
  congr 1
  dsimp only [T,pairOmittedIntegrand]
  ring

/-- Actual second beta partials vanish whenever their total depth exceeds
the remaining screening degree, with no separate index-bound assumption. -/
theorem state_beta_double_above_degree (r q M a b : ℕ) (hq : 0<q)
    (hab : r*(q-1)<a+b) :
    pderiv (0,b) (pderiv (0,a) (state r q M))=0 := by
  by_cases ha : a≤r*(q-1)
  · by_cases hb : b≤r*(q-1)
    · rw [state_beta_double_partial r q M a b ha hb]
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      exact selected_pair_above_degree r q M a b hq hab i j
    · rw [pderiv_comm',state_beta_derivative_above r q M b (by omega),map_zero]
  · rw [state_beta_derivative_above r q M a (by omega),map_zero]

/-- The finite divided difference is exactly the sum of two-monomial
insertions with total depth equal to its beta creation depth. -/
theorem betaDivided_as_singles (r N : ℕ) (i j : Fin r) :
    betaDivided r N i j=∑ d∈Finset.range (N+1),∑ a∈Finset.range (d+1),
      (single 0 (X (0,d)) : Auxiliary r)*
        single ((a : ℤ) • unitExponent r i) 1*
        single (((d-a : ℕ) : ℤ) • unitExponent r j) 1 := by
  rw [betaDivided]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [auxiliaryVariable,single_pow,one_pow]
  simp [nsmul_eq_mul,zsmul_eq_mul,mul_assoc]

/-- The actual finite quadratic beta sum is the ordered pair divided-
difference sum, with no implicit conversion to unordered pairs. -/
theorem state_quadratic_sum_selected (r q M : ℕ) :
    (∑ d∈Finset.range (r*(q-1)+1),X (0,d)*
      ∑ a∈Finset.range (d+1),pderiv (0,d-a) (pderiv (0,a) (state r q M)))=
    ∑ i : Fin r,∑ j∈Finset.univ.erase i,
      (betaDivided r (r*(q-1)) i j*pairOmittedIntegrand r q M i j)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  classical
  have hterm (d : ℕ) (hd : d∈Finset.range (r*(q-1)+1))
      (a : ℕ) (ha : a∈Finset.range (d+1)) :=
    state_beta_double_partial r q M a (d-a)
      (by have := Finset.mem_range.mp hd; have := Finset.mem_range.mp ha; omega)
      (by have := Finset.mem_range.mp hd; omega)
  calc
    _ = ∑ d∈Finset.range (r*(q-1)+1),∑ a∈Finset.range (d+1),
      ∑ i : Fin r,∑ j∈Finset.univ.erase i,
        (((single 0 (X (0,d)) : Auxiliary r)*single ((a : ℤ) • unitExponent r i) 1*
          single (((d-a : ℕ) : ℤ) • unitExponent r j) 1)*pairOmittedIntegrand r q M i j : Auxiliary r)
          (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hterm d hd a ha,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← selected_constant_mul]
      congr 1
      ring
    _ = _ := by
      simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.univ.erase i)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [betaDivided_as_singles,Finset.sum_mul,auxiliary_sum_apply]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul,auxiliary_sum_apply]

end
end VOA.Wak.Screening
