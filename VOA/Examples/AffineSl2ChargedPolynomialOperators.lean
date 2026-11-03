/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoCharged
import Mathlib.Algebra.Polynomial.Module.Basic

/-!
# Polynomial dependence of actual charged currents

The highest weight is retained as a polynomial variable, with coefficients
in the actual Wakimoto carrier. Evaluation recovers the actual currents.
Coefficient bounds and leading coefficients can therefore be proved before
specializing the highest weight; no generic representation is postulated.
-/
namespace VOA.Wak.Charged
open Module (End)
noncomputable section

/-- Finite highest-weight polynomials with actual Fock vectors as coefficients. -/
abbrev FockPolynomial := PolynomialModule ℂ WakFock

/-- The coefficient of the highest weight in a charged current. Only F and
H-zero have such a coefficient; E is independent of the highest weight. -/
def chargeLinear (a : Fin 3) (n : ℤ) : End ℂ WakFock :=
  if a=0 then 0 else if a=1 then Gam n else if n=0 then 1 else 0

/-- Exact affine-linear dependence of the actual current on highest weight. -/
theorem J_charge_linear (k h : ℂ) (a : Fin 3) (n : ℤ) :
    J k h a n=J k 0 a n+h • chargeLinear a n := by
  fin_cases a <;> simp [J,F,H,chargeLinear] <;> split_ifs <;> module

/-- Apply a current while keeping its highest weight formal. The constant
part acts coefficientwise and the linear part raises polynomial degree by one. -/
def polynomialCurrent (k : ℂ) (a : Fin 3) (n : ℤ)
    (P : FockPolynomial) : FockPolynomial :=
  PolynomialModule.map ℂ (J k 0 a n) P +
    (Polynomial.X : Polynomial ℂ) • PolynomialModule.map ℂ (chargeLinear a n) P

/-- Evaluation of the formal current is the actual charged current on the
evaluated Fock vector, for every complex level and highest weight. -/
theorem polynomialCurrent_eval (k h : ℂ) (a : Fin 3) (n : ℤ)
    (P : FockPolynomial) :
    PolynomialModule.eval h (polynomialCurrent k a n P)=
      J k h a n (PolynomialModule.eval h P) := by
  rw [polynomialCurrent,map_add,PolynomialModule.eval_smul,J_charge_linear k h a n]
  simp only [Polynomial.eval_X,PolynomialModule.eval_map',
    LinearMap.add_apply,LinearMap.smul_apply]

/-- The constant coefficient has no contribution from the linear charge term. -/
theorem polynomialCurrent_zero (k : ℂ) (a : Fin 3) (n : ℤ)
    (P : FockPolynomial) :
    polynomialCurrent k a n P 0=J k 0 a n (P 0) := by
  simp only [polynomialCurrent,PolynomialModule.add_apply,Polynomial.X,
    PolynomialModule.monomial_smul_apply]
  simp [PolynomialModule.map]
  rfl

/-- At a positive polynomial exponent the current has exactly two adjacent
coefficient contributions. This includes horizontal modes and zero coefficients. -/
theorem polynomialCurrent_succ (k : ℂ) (a : Fin 3) (n : ℤ)
    (P : FockPolynomial) (j : ℕ) :
    polynomialCurrent k a n P (j+1)=
      J k 0 a n (P (j+1))+chargeLinear a n (P j) := by
  simp only [polynomialCurrent,PolynomialModule.add_apply,Polynomial.X,
    PolynomialModule.monomial_smul_apply]
  simp [PolynomialModule.map]
  rfl

/-- A coefficient bound without a degree convention for the zero polynomial. -/
def FockDegreeLE (d : ℕ) (P : FockPolynomial) : Prop := ∀ j,d<j→P j=0

/-- A charged current raises polynomial degree by at most one. -/
theorem polynomialCurrent_degree (k : ℂ) (a : Fin 3) (n : ℤ)
    {P : FockPolynomial} {d : ℕ} (hP : FockDegreeLE d P) :
    FockDegreeLE (d+1) (polynomialCurrent k a n P) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j =>
    rw [polynomialCurrent_succ,hP (j+1) (by omega),hP j (by omega)]
    simp

/-- The newly possible top coefficient is precisely the linear charge
operator applied to the old top coefficient; all constant-current terms vanish. -/
theorem polynomialCurrent_top (k : ℂ) (a : Fin 3) (n : ℤ)
    {P : FockPolynomial} {d : ℕ} (hP : FockDegreeLE d P) :
    polynomialCurrent k a n P (d+1)=chargeLinear a n (P d) := by
  rw [polynomialCurrent_succ,hP (d+1) (by omega),map_zero,zero_add]

/-- If the current has no linear charge term, it preserves the old bound. -/
theorem polynomialCurrent_degree_constant (k : ℂ) (a : Fin 3) (n : ℤ)
    (hz : chargeLinear a n=0) {P : FockPolynomial} {d : ℕ}
    (hP : FockDegreeLE d P) : FockDegreeLE d (polynomialCurrent k a n P) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j => rw [polynomialCurrent_succ,hz,hP (j+1) hj]; simp

/-- For a charge-independent current the old top coefficient is acted on
by the actual current at zero highest weight. -/
theorem polynomialCurrent_top_constant (k : ℂ) (a : Fin 3) (n : ℤ)
    (hz : chargeLinear a n=0) (P : FockPolynomial) (d : ℕ) :
    polynomialCurrent k a n P d=J k 0 a n (P d) := by
  cases d with
  | zero => exact polynomialCurrent_zero k a n P
  | succ d => rw [polynomialCurrent_succ,hz]; simp

end
end VOA.Wak.Charged
