/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningOmittedIBP

/-!
# Actual beta partials as omitted-factor expressions

Finite Leibniz expresses beta differentiation by deleting a single beta
factor and inserting its auxiliary monomial. Coefficient extraction then
identifies the actual oscillator partials of the screening state.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Exact finite Leibniz expansion: differentiate one factor and multiply
by the product with that factor erased. No division by a factor is used. -/
theorem derivative_prod_omissions {r : ℕ} {I : Type*} [DecidableEq I]
    (D : Derivation ℂ (Auxiliary r) (Auxiliary r)) (S : Finset I) (P : I → Auxiliary r) :
    D (∏ i∈S,P i)=∑ i∈S,D (P i)*(∏ j∈S.erase i,P j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,D.map_one_eq_zero,Finset.sum_empty]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi,D.leibniz,ih,Finset.sum_insert hi,Finset.erase_insert hi]
      simp only [smul_eq_mul,Finset.mul_sum]
      rw [add_comm]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j hj
        have hji : j≠i := by intro h; subst j; exact hi hj
        rw [Finset.erase_insert_of_ne (Ne.symm hji),Finset.prod_insert (by
          intro h; exact hi (Finset.mem_of_mem_erase h))]
        ring

/-- A beta partial within the cutoff differentiates the whole beta
product by inserting one auxiliary monomial in each omitted-factor term. -/
theorem beta_product_partial_omissions (r N d : ℕ) (hd : d≤N) :
    oscillatorPartial r (0,d) (∏ i : Fin r,betaFactor r N i)=
      ∑ i : Fin r,(single ((d : ℤ) • unitExponent r i) 1 : Auxiliary r)*
        (∏ j∈Finset.univ.erase i,betaFactor r N j) := by
  rw [derivative_prod_omissions]
  apply Finset.sum_congr rfl
  intro i hi
  rw [oscillatorPartial_betaFactor,if_pos hd]

/-- The actual beta derivative of the whole integrand is a finite sum
of omitted integrands with the corresponding auxiliary monomial inserted. -/
theorem integrand_beta_partial_omissions (r q M d : ℕ) (hd : d≤r*(q-1)) :
    oscillatorPartial r (0,d) (integrand r q M)=
      ∑ i : Fin r,(single ((d : ℤ) • unitExponent r i) 1 : Auxiliary r)*
        omittedIntegrand r q M i := by
  have he := derivative_prod_zero (oscillatorPartial r (0,d))
    (Finset.range (r*(q-1))) (fun m => exponentialFactor r (r*(q-1)) M (m+1))
    (fun m _ => oscillatorPartial_exponentialFactor_beta r _ M _ d)
  rw [integrand,(oscillatorPartial r (0,d)).leibniz,he,
    (oscillatorPartial r (0,d)).leibniz,
    (oscillatorPartial r (0,d)).leibniz_pow,oscillatorPartial_delta,
    beta_product_partial_omissions r _ d hd]
  simp only [smul_zero,add_zero,smul_eq_mul,mul_zero,zero_add,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [omittedIntegrand]
  ring

/-- Selecting a coefficient of a finite auxiliary sum is the sum of
selected actual oscillator coefficients. -/
theorem auxiliary_sum_apply {r : ℕ} {I : Type*} (S : Finset I)
    (P : I → Auxiliary r) (g : Fin r → ℤ) :
    (∑ i∈S,P i) g=∑ i∈S,P i g := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      change P i g+(∑ j∈S,P j) g=_
      rw [ih]

/-- An actual beta partial of the screening vector equals the finite sum
of selected omitted-factor expressions. The depth is inside the cutoff. -/
theorem state_beta_partial_omissions (r q M d : ℕ) (hd : d≤r*(q-1)) :
    pderiv (0,d) (state r q M)=
      ∑ i : Fin r,((single ((d : ℤ) • unitExponent r i) 1 : Auxiliary r)*
        omittedIntegrand r q M i) (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  rw [state,← oscillatorPartial_apply,integrand_beta_partial_omissions r q M d hd,
    auxiliary_sum_apply]

/-- The first beta annihilation mode is exactly the sum of the selected
omitted integrands, with no auxiliary monomial shift. -/
theorem state_beta_one_omissions (r q M : ℕ) :
    bD 1 (state r q M)=∑ i : Fin r,omittedIntegrand r q M i
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ)) := by
  rw [bD_of_pos (by omega : (1 : ℤ)≤1),dV_apply]
  have h := state_beta_partial_omissions r q M 0 (by omega)
  simpa only [Int.sub_self,Int.toNat_zero,Nat.cast_zero,zero_smul,
    ← AddMonoidAlgebra.one_def,one_mul] using h

end
end VOA.Wak.Screening
