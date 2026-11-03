/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoCharged
import VOA.Examples.VirasoroScreeningVandermonde

/-!
# A finite polynomial for integer affine screenings

The auxiliary Laurent variables only organize a finite coefficient extraction.
The resulting vector belongs to the actual Wakimoto polynomial space. Setting
one beta creation variable to one and all other oscillators to zero reduces
its value to the nonzero central Vandermonde coefficient. This proves a genuine
nonzero vector, but does not yet prove the affine Ward equations.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening
open scoped BigOperators

/-- Auxiliary finite Laurent expressions with actual Wakimoto polynomials as
coefficients. There is no analytic convergence or contour choice. -/
abbrev Auxiliary (r : ℕ) := AddMonoidAlgebra WakFock (Fin r → ℤ)

/-- Embed the rational Vandermonde coefficients as constant oscillator polynomials. -/
noncomputable def rationalConstants : ℚ →+* WakFock :=
  MvPolynomial.C.comp (algebraMap ℚ ℂ)

/-- The auxiliary Vandermonde in the polynomial coefficient ring. -/
noncomputable def delta (r : ℕ) : Auxiliary r :=
  AddMonoidAlgebra.mapRingHom _ rationalConstants (vandermondeLaurent r)

/-- Finite beta creation series, through the specified auxiliary degree. -/
noncomputable def betaFactor (r D : ℕ) (i : Fin r) : Auxiliary r :=
  ∑ j ∈ Finset.range (D+1),
    single ((j : ℤ) • unitExponent r i) (MvPolynomial.X (0,j))

/-- The m-th auxiliary power sum multiplied by the matching boson creation
variable. The application below only uses positive m. -/
noncomputable def bosonPower (r m : ℕ) : Auxiliary r :=
  ∑ i : Fin r, single ((m : ℤ) • unitExponent r i) (MvPolynomial.X (2,m-1))

/-- A finite exponential factor with the explicit screening coefficient
(-M/m)^ell/ell!. Truncation is part of the definition, not an infinite-series claim. -/
noncomputable def exponentialFactor (r D M m : ℕ) : Auxiliary r :=
  ∑ ell ∈ Finset.range (D+1),
    single 0 (MvPolynomial.C (((-(M : ℂ)/(m : ℂ))^ell)/(ell.factorial : ℂ))) *
      bosonPower r m ^ ell

/-- Finite integrand: an even Vandermonde power, r beta factors and the
truncated boson exponential. The remaining auxiliary degree is r(q-1). -/
noncomputable def integrand (r q M : ℕ) : Auxiliary r :=
  delta r ^ (2*M) * (∏ i : Fin r, betaFactor r (r*(q-1)) i) *
    ∏ m ∈ Finset.range (r*(q-1)), exponentialFactor r (r*(q-1)) M (m+1)

/-- The actual polynomial vector obtained by selecting the common auxiliary
exponent (r-1)M+q-1. Its nonvanishing below needs positive rank and q. -/
noncomputable def state (r q M : ℕ) : WakFock :=
  integrand r q M (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))

/-- Test a screening vector by setting beta at depth q-1 to one and every
other oscillator to zero. This is a ring homomorphism, not an inner product. -/
noncomputable def survival (q : ℕ) : WakFock →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v => if v=(0,q-1) then 1 else 0)

/-- Coefficientwise extension of the oscillator test to auxiliary expressions. -/
noncomputable def test (r q : ℕ) : Auxiliary r →+* AddMonoidAlgebra ℂ (Fin r → ℤ) :=
  AddMonoidAlgebra.mapRingHom _ (survival q)

/-- Constants survive the oscillator evaluation unchanged. -/
@[simp] theorem survival_C (q : ℕ) (z : ℂ) : survival q (MvPolynomial.C z)=z := by
  simp [survival]

/-- The chosen beta oscillator is the only surviving generator. -/
@[simp] theorem survival_X (q : ℕ) (v : Fin 3 × ℕ) :
    survival q (MvPolynomial.X v) = if v=(0,q-1) then 1 else 0 := by
  simp [survival]

/-- Testing the lifted rational Vandermonde agrees coefficientwise with
ordinary complexification. -/
theorem test_delta (r q : ℕ) : test r q (delta r) =
    AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) (vandermondeLaurent r) := by
  ext g
  simp [test,delta,rationalConstants]

/-- The beta series becomes the single monomial z_i^(q-1), provided that
its truncation includes this exponent. -/
theorem test_betaFactor (r D q : ℕ) (i : Fin r) (h : q-1≤D) :
    test r q (betaFactor r D i) = single (((q-1 : ℕ) : ℤ) • unitExponent r i) 1 := by
  classical
  simp only [test,betaFactor,map_sum,AddMonoidAlgebra.mapRingHom_single,survival_X,
    Prod.mk.injEq,true_and]
  rw [Finset.sum_eq_single (q-1)]
  · simp
  · intro b hb hbq
    simp [hbq]
    rfl
  · simp [Finset.mem_range,Nat.lt_succ_of_le h]

/-- All boson variables vanish under the survival test. -/
theorem test_bosonPower (r q m : ℕ) : test r q (bosonPower r m)=0 := by
  classical
  simp [test,bosonPower,show (2 : Fin 3)≠0 by decide]
  exact Or.inr rfl

/-- Each truncated exponential has tested value one: all positive powers
contain a boson variable, and its constant term is one. -/
theorem test_exponentialFactor (r D q M m : ℕ) :
    test r q (exponentialFactor r D M m)=1 := by
  classical
  simp only [exponentialFactor,map_sum,map_mul,map_pow,test_bosonPower]
  rw [Finset.sum_eq_single 0]
  · simp [test,← AddMonoidAlgebra.one_def]
  · intro b hb hb0
    simp [zero_pow hb0]
  · simp

/-- Summing the auxiliary unit exponents gives a constant exponent vector. -/
theorem sum_unitExponent (r : ℕ) (a : ℤ) :
    (∑ i : Fin r, a • unitExponent r i) = fun _ => a := by
  classical
  ext j
  simp [unitExponent,Pi.single_apply]

/-- The survival test removes the boson exponential and shifts the
Vandermonde by exactly q-1 in each variable. -/
theorem test_integrand (r q M : ℕ) (hr : 0 < r) :
    test r q (integrand r q M) =
      AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) (vandermondeLaurent r^(2*M)) *
        single (fun _ => ((q-1 : ℕ) : ℤ)) 1 := by
  classical
  have hD : q-1≤r*(q-1) := by nlinarith
  simp only [integrand,map_mul,map_pow,map_prod,test_delta,
    test_betaFactor r (r*(q-1)) q _ hD,test_exponentialFactor,
    Finset.prod_const_one,mul_one]
  rw [AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one,sum_unitExponent,map_pow]

/-- The actual screening polynomial evaluates to the nonzero middle
Vandermonde coefficient. No normalization product is assumed. -/
theorem survival_state (r q M : ℕ) (hr : 0 < r) (hq : 0 < q) :
    survival q (state r q M) =
      ((vandermondeLaurent r^(2*M)) (fun _ => (((r-1)*M : ℕ) : ℤ)) : ℂ) := by
  have h := congrArg (fun P : AddMonoidAlgebra ℂ (Fin r → ℤ) =>
    P (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))) (test_integrand r q M hr)
  dsimp only at h
  rw [AddMonoidAlgebra.mul_single_apply] at h
  have he : (fun _ : Fin r => (((r-1)*M+q-1 : ℕ) : ℤ)) -
      (fun _ => ((q-1 : ℕ) : ℤ)) = fun _ => (((r-1)*M : ℕ) : ℤ) := by
    ext i
    simp only [Pi.sub_apply]
    omega
  rw [← sub_eq_add_neg,he,AddMonoidAlgebra.mapRingHom_apply,mul_one] at h
  exact h

/-- A genuine nonzero vector in the charged Wakimoto polynomial space at
every positive rank and q and every natural integer screening exponent M.
Singularity under affine positive modes is a separate theorem still needed. -/
theorem state_ne_zero (r q M : ℕ) (hr : 0 < r) (hq : 0 < q) : state r q M≠0 := by
  intro hz
  have h := survival_state r q M hr hq
  rw [hz,map_zero] at h
  have hc := vandermonde_central_coefficient_ne_zero r M
  exact hc (by exact_mod_cast h.symm)

end VOA.Wak.Screening
