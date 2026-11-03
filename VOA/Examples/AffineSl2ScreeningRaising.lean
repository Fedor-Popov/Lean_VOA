/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningGrading

/-!
# Actual raising-mode annihilation of the screening vector

The finite integrand contains beta and boson creation variables only.
Closure under finite coefficient convolution makes that assertion precise:
every gamma partial derivative vanishes. The actual nonnegative raising
current is exactly such a partial derivative, including the zero mode.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Oscillator polynomials independent of every gamma variable. The Leibniz
rule makes this the simultaneous kernel subalgebra of all gamma partials. -/
def gammaFree : Subalgebra ℂ WakFock where
  carrier := {p | ∀ j, pderiv (1,j) p=0}
  algebraMap_mem' z := by intro j; simp
  zero_mem' := by intro j; simp
  add_mem' hp hq := by intro j; simp only [map_add,hp j,hq j,add_zero]
  one_mem' := by intro j; simp
  mul_mem' hp hq := by intro j; rw [pderiv_mul,hp j,hq j,zero_mul,mul_zero,add_zero]

/-- An auxiliary expression whose every coefficient belongs to a fixed
oscillator subalgebra. Finite convolution preserves this condition. -/
def coefficientAlgebra (r : ℕ) (S : Subalgebra ℂ WakFock) : Subalgebra ℂ (Auxiliary r) where
  carrier := {P | ∀ g, P g∈S}
  algebraMap_mem' z := by
    intro g
    rw [Algebra.algebraMap_eq_smul_one]
    change (z • (1 : Auxiliary r)) g∈S
    rw [AddMonoidAlgebra.smul_apply,AddMonoidAlgebra.one_def]
    classical
    by_cases h : (0 : Fin r → ℤ)=g
    · subst g; simpa using S.smul_mem (S.one_mem) z
    · simp [AddMonoidAlgebra.single_apply,h]
  zero_mem' := by intro g; exact S.zero_mem
  add_mem' hp hq := by intro g; exact S.add_mem (hp g) (hq g)
  one_mem' := by
    intro g
    classical
    rw [AddMonoidAlgebra.one_def]
    by_cases h : (0 : Fin r → ℤ)=g
    · subst g; simpa using S.one_mem
    · simp [AddMonoidAlgebra.single_apply,h]
  mul_mem' hp hq := by
    intro g
    classical
    rw [AddMonoidAlgebra.mul_apply]
    apply S.sum_mem
    intro x hx
    apply S.sum_mem
    intro y hy
    dsimp only
    split_ifs
    · exact S.mul_mem (hp x) (hq y)
    · exact S.zero_mem

/-- A single auxiliary monomial lies in the coefficient subalgebra when
its oscillator coefficient does. -/
theorem single_mem_coefficientAlgebra (r : ℕ) (S : Subalgebra ℂ WakFock)
    (g : Fin r → ℤ) (p : WakFock) (hp : p∈S) :
    single g p∈coefficientAlgebra r S := by
  intro x
  classical
  by_cases h : g=x
  · subst x; simpa using hp
  · simp [AddMonoidAlgebra.single_apply,h]

/-- Beta and boson creation generators have no gamma dependence. -/
theorem X_mem_gammaFree (a : Fin 3) (j : ℕ) (ha : a≠1) :
    MvPolynomial.X (a,j)∈gammaFree := by
  intro i
  exact pderiv_X_of_ne (by intro h; exact ha (congrArg Prod.fst h))

/-- Every coefficient of the rational Vandermonde is gamma-independent. -/
theorem delta_gammaFree (r : ℕ) : delta r∈coefficientAlgebra r gammaFree := by
  intro g j
  simp [delta,rationalConstants]

/-- Each finite beta factor is gamma-independent coefficientwise. -/
theorem betaFactor_gammaFree (r D : ℕ) (i : Fin r) :
    betaFactor r D i∈coefficientAlgebra r gammaFree := by
  apply (coefficientAlgebra r gammaFree).sum_mem
  intro j hj
  exact single_mem_coefficientAlgebra r gammaFree _ _ (X_mem_gammaFree 0 j (by decide))

/-- The boson power sum is gamma-independent coefficientwise. -/
theorem bosonPower_gammaFree (r m : ℕ) : bosonPower r m∈coefficientAlgebra r gammaFree := by
  apply (coefficientAlgebra r gammaFree).sum_mem
  intro i hi
  exact single_mem_coefficientAlgebra r gammaFree _ _ (X_mem_gammaFree 2 _ (by decide))

/-- Every finite exponential factor remains gamma-independent. -/
theorem exponentialFactor_gammaFree (r D M m : ℕ) :
    exponentialFactor r D M m∈coefficientAlgebra r gammaFree := by
  apply (coefficientAlgebra r gammaFree).sum_mem
  intro ell hell
  apply (coefficientAlgebra r gammaFree).mul_mem
  · apply single_mem_coefficientAlgebra
    intro j
    simp
  · exact (coefficientAlgebra r gammaFree).pow_mem (bosonPower_gammaFree r m) ell

/-- All coefficients of the complete finite screening integrand are
independent of every gamma oscillator. -/
theorem integrand_gammaFree (r q M : ℕ) : integrand r q M∈coefficientAlgebra r gammaFree := by
  apply (coefficientAlgebra r gammaFree).mul_mem
  · apply (coefficientAlgebra r gammaFree).mul_mem
    · exact (coefficientAlgebra r gammaFree).pow_mem (delta_gammaFree r) _
    · exact (coefficientAlgebra r gammaFree).prod_mem (fun i _ => betaFactor_gammaFree r _ i)
  · exact (coefficientAlgebra r gammaFree).prod_mem (fun m _ => exponentialFactor_gammaFree r _ M _)

/-- Every gamma partial derivative of the actual screening vector is zero. -/
theorem state_gamma_derivative (r q M j : ℕ) : pderiv (1,j) (state r q M)=0 :=
  integrand_gammaFree r q M _ j

/-- Every actual nonnegative raising mode kills the screening vector,
including the horizontal raising operator E_0. No singularity assumption
or condition on level and highest weight is used. -/
theorem state_raising (r q M : ℕ) (n : ℤ) (hn : 0≤n) :
    Ecur n (state r q M)=0 := by
  rw [Ecur,Bet_of_nonneg hn,cD_of_nonneg hn,dV_apply]
  exact state_gamma_derivative r q M n.toNat

/-- Scalar multiplication distributes through the actual endomorphism
commutator. This local identity fixes the imported Lie instance explicitly. -/
private theorem smul_commutator (a : ℂ) (S T : Module.End ℂ WakFock) :
    ⁅a • S,T⁆=a • ⁅S,T⁆ := by
  rw [Ring.lie_def,Ring.lie_def,mul_smul_comm,smul_mul_assoc,smul_sub]

/-- The ordinary Cartan zero mode is exactly twice the ghost-charge Euler
operator on every Wakimoto polynomial, not only on a highest vector. -/
theorem Hcur_zero_eq (k : ℂ) : Hcur k 0 = (2 : ℂ) • Dch := by
  let S := Hcur k 0 - (2 : ℂ) • Dch
  have hb : ∀ n : ℤ, ⁅S,Bet n⁆=0 := by
    intro n
    dsimp only [S]
    rw [sub_lie,smul_commutator,Hcur_lie_Bet,Dch_lie_Bet,zero_add,sub_self]
  have hg : ∀ n : ℤ, ⁅S,Gam n⁆=0 := by
    intro n
    dsimp only [S]
    rw [sub_lie,smul_commutator,Hcur_lie_Gam,Dch_lie_Gam,zero_add]
    module
  have ha : ∀ n : ℤ, ⁅S,Aos k n⁆=0 := by
    intro n
    dsimp only [S]
    rw [sub_lie,smul_commutator,Hcur_lie_Aos,Dch_lie_Aos]
    simp
  have hs := eq_mulL_of_lie_modes hb hg ha
  have hz : S (1 : WakFock)=0 := by
    dsimp only [S]
    rw [LinearMap.sub_apply,LinearMap.smul_apply,Hcur_one k (by omega),Dch,Eul_one',smul_zero,sub_zero]
  rw [hz,mulL_zero] at hs
  exact sub_eq_zero.mp hs

/-- The charged Cartan zero mode gives the actual screening vector weight
lambda+2r. This identifies its joint weight together with state_energy. -/
theorem state_cartan (r q M : ℕ) (k lam : ℂ) :
    Charged.H k lam 0 (state r q M) = (lam+2*r) • state r q M := by
  rw [Charged.H,if_pos rfl,Hcur_zero_eq]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,state_charge,smul_smul]
  module

end
end VOA.Wak.Screening
