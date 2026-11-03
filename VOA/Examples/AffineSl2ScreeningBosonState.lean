/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningProductDerivative

/-!
# Boson differentiation of the whole finite screening state

The finite product rule combines all exponential factors. Every terminal
correction is above the auxiliary cutoff. Modes outside the cutoff vanish
by actual oscillator independence and auxiliary support, respectively.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The full beta product has zero boson partial. -/
theorem boson_partial_beta_product (r D m : ℕ) :
    oscillatorPartial r (2,m) (∏ i : Fin r,betaFactor r D i)=0 := by
  exact derivative_prod_zero _ _ _ (fun i _ => oscillatorPartial_betaFactor_boson r D m i)

/-- The matching exponential factor satisfies the multiplier equation
up to an error above the cutoff. -/
theorem exponential_boson_error (r D M m : ℕ) (hm : 0<m) :
    LowerDegree (D+1 : ℤ) (oscillatorPartial r (2,m-1) (exponentialFactor r D M m)-
      ((-(M : ℂ)/m) • auxiliaryPowerSum r m)*exponentialFactor r D M m) := by
  have he := exponentialFactor_boson_derivative r D M m
  have hl := (exponential_derivative_error_lower r D M m).neg
  have hh : (D : ℤ)+1≤(m : ℤ)*(D+1) := by
    have hmi : (1 : ℤ)≤m := by omega
    have hdi : (0 : ℤ)≤D := by positivity
    nlinarith
  convert hl.mono hh using 1
  rw [smul_mul_assoc]
  linear_combination he

/-- When the mode lies in the cutoff, the entire exponential product
has its power-sum multiplier modulo an error above the cutoff. -/
theorem boson_exponential_product_error (r D M m : ℕ) (hm : 0<m) (hmd : m≤D) :
    LowerDegree (D+1 : ℤ)
      (oscillatorPartial r (2,m-1)
        (∏ j∈Finset.range D,exponentialFactor r D M (j+1))-
       ((-(M : ℂ)/m) • auxiliaryPowerSum r m)*
        (∏ j∈Finset.range D,exponentialFactor r D M (j+1))) := by
  classical
  have he := derivative_error_prod (oscillatorPartial r (2,m-1)) (D+1 : ℤ)
    (Finset.range D) (fun j => exponentialFactor r D M (j+1))
    (fun j => if j+1=m then (-(M : ℂ)/m) • auxiliaryPowerSum r m else 0)
    (fun j _ => exponentialFactor_lower r D M (j+1)) (by
      intro j hj
      dsimp only
      by_cases h : j+1=m
      · rw [if_pos h,h]; exact exponential_boson_error r D M m hm
      · rw [if_neg h,zero_mul,sub_zero,
          exponentialFactor_boson_derivative_ne r D M m (j+1) hm (by omega) (Ne.symm h)]
        exact LowerDegree.zero r _)
  have hs : (∑ j∈Finset.range D,
      if j+1=m then (-(M : ℂ)/m) • auxiliaryPowerSum r m else 0)=
      (-(M : ℂ)/m) • auxiliaryPowerSum r m := by
    rw [Finset.sum_eq_single (m-1)]
    · rw [if_pos (by omega)]
    · intro j hj hne; rw [if_neg (by omega)]
    · intro h; exact False.elim (h (Finset.mem_range.mpr (by omega)))
  rwa [hs] at he

/-- A boson mode above the cutoff differentiates every exponential factor
to zero, and hence kills the whole exponential product exactly. -/
theorem boson_exponential_product_above (r D M m : ℕ) (hmd : D<m) :
    oscillatorPartial r (2,m-1)
      (∏ j∈Finset.range D,exponentialFactor r D M (j+1))=0 := by
  apply derivative_prod_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact exponentialFactor_boson_derivative_ne r D M m (j+1) (by omega) (by omega) (by omega)

/-- Differentiating the actual whole integrand reduces to differentiating
its exponential product; the Vandermonde and beta factors contribute zero. -/
theorem boson_partial_integrand (r q M m : ℕ) :
    oscillatorPartial r (2,m-1) (integrand r q M)=
      delta r^(2*M)*((∏ i : Fin r,betaFactor r (r*(q-1)) i)*
        oscillatorPartial r (2,m-1)
          (∏ j∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (j+1))) := by
  rw [integrand,(oscillatorPartial r (2,m-1)).leibniz,
    (oscillatorPartial r (2,m-1)).leibniz,
    (oscillatorPartial r (2,m-1)).leibniz_pow,
    oscillatorPartial_delta,boson_partial_beta_product]
  simp only [smul_zero,add_zero,zero_smul,zero_add,smul_eq_mul,mul_assoc,mul_zero]


/-- Inside the cutoff, the actual boson derivative of the complete
screening state is its auxiliary power-sum insertion. All finite terminal
corrections have been excluded by the proved support estimate. -/
theorem state_boson_derivative_within (r q M m : ℕ) (hq : 0<q)
    (hm : 0<m) (hmd : m≤r*(q-1)) :
    pderiv (2,m-1) (state r q M)=(-(M : ℂ)/m) •
      ((auxiliaryPowerSum r m*integrand r q M)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  let B := ∏ i : Fin r,betaFactor r (r*(q-1)) i
  let E := ∏ j∈Finset.range (r*(q-1)),exponentialFactor r (r*(q-1)) M (j+1)
  let a := (-(M : ℂ)/m) • auxiliaryPowerSum r m
  let D := oscillatorPartial r (2,m-1)
  have hb : LowerDegree 0 B := lowerDegree_prod_zero _ _ (fun i _ => betaFactor_lower r _ i)
  have he : LowerDegree ((r*(q-1) : ℕ)+1 : ℤ) (D E-a*E) :=
    boson_exponential_product_error r _ M m hm hmd
  have hc : (((r*(q-1) : ℕ) : ℤ)+1)=(r : ℤ)*(q-1)+1 := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
  rw [hc] at he
  have herr : LowerDegree ((r : ℤ)*(q-1)+1) (B*(D E-a*E)) := by
    simpa using hb.mul he
  have hz := screening_high_degree_zero r q M hq _ herr
  have ha : D (integrand r q M)-a*integrand r q M=
      delta r^(2*M)*(B*(D E-a*E)) := by
    dsimp only [D]
    rw [boson_partial_integrand,integrand]
    dsimp only [B,E]
    ring
  rw [← ha] at hz
  change (D (integrand r q M)) _-(a*integrand r q M) _=0 at hz
  rw [oscillatorPartial_apply] at hz
  have hs := sub_eq_zero.mp hz
  rw [show a*integrand r q M=(-(M : ℂ)/m) •
    (auxiliaryPowerSum r m*integrand r q M) by exact smul_mul_assoc _ _ _] at hs
  exact hs

/-- Above the finite boson cutoff, the actual state is independent of
the oscillator, so its partial derivative is exactly zero. -/
theorem state_boson_derivative_above (r q M m : ℕ) (hmd : r*(q-1)<m) :
    pderiv (2,m-1) (state r q M)=0 := by
  rw [state,← oscillatorPartial_apply,boson_partial_integrand,
    boson_exponential_product_above r _ M m hmd,mul_zero,mul_zero]
  rfl

/-- A power-sum insertion above the remaining auxiliary degree has zero
selected coefficient in the complete integrand. -/
theorem state_powerSum_above (r q M m : ℕ) (hq : 0<q) (hmd : r*(q-1)<m) :
    (auxiliaryPowerSum r m*integrand r q M)
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  have hp : LowerDegree ((r : ℤ)*(q-1)+1) (auxiliaryPowerSum r m) := by
    apply (auxiliaryPowerSum_lower r m).mono
    have hc : (((r*(q-1) : ℕ) : ℤ)+1)=(r : ℤ)*(q-1)+1 := by
      rw [Nat.cast_mul,Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
    rw [← hc]
    exact_mod_cast hmd
  have hz := screening_high_degree_product_zero r q M hq _ _ hp
    (screening_factors_lower r q M)
  convert hz using 1
  rw [integrand]
  ring

/-- For EVERY positive boson mode, differentiation of the actual screening
state equals the finite auxiliary power-sum insertion with coefficient -M/m.
This includes modes above the truncation bound, where both sides vanish. -/
theorem state_boson_derivative (r q M m : ℕ) (hq : 0<q) (hm : 0<m) :
    pderiv (2,m-1) (state r q M)=(-(M : ℂ)/m) •
      ((auxiliaryPowerSum r m*integrand r q M)
        (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) := by
  by_cases hmd : m≤r*(q-1)
  · exact state_boson_derivative_within r q M m hq hm hmd
  · rw [state_boson_derivative_above r q M m (by omega),
      state_powerSum_above r q M m hq (by omega),smul_zero]

end
end VOA.Wak.Screening
