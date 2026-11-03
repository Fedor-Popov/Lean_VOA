/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningDividedDifference
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Actual coefficientwise oscillator differentiation

Oscillator derivations extend coefficientwise to the finite auxiliary Laurent
algebra. The finite exponential has an exact terminal correction term. No
infinite power series or discarded boundary term is used in these identities.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Extend an actual oscillator derivation to each auxiliary coefficient. -/
def coefficientDerivative (r : ℕ) (D : Derivation ℂ WakFock WakFock) :
    Auxiliary r →ₗ[ℂ] Auxiliary r :=
  Finsupp.lsum ℂ (fun g => (Finsupp.lsingle g).comp D.toLinearMap)

/-- A single auxiliary monomial keeps its exponent while its oscillator
coefficient is differentiated. -/
theorem coefficientDerivative_single (r : ℕ) (D : Derivation ℂ WakFock WakFock)
    (g : Fin r → ℤ) (p : WakFock) :
    coefficientDerivative r D (single g p)=single g (D p) := by
  change (Finsupp.lsum ℂ (fun g : Fin r → ℤ =>
    (Finsupp.lsingle g).comp D.toLinearMap)) (Finsupp.single g p)=_
  rw [Finsupp.lsum_single]
  rfl

/-- Coefficient extraction commutes exactly with oscillator differentiation. -/
theorem coefficientDerivative_apply (r : ℕ) (D : Derivation ℂ WakFock WakFock)
    (P : Auxiliary r) (g : Fin r → ℤ) : coefficientDerivative r D P g=D (P g) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; change (0 : WakFock)=D 0; rw [map_zero]
  | add P Q hP hQ =>
      rw [map_add]
      change coefficientDerivative r D P g+coefficientDerivative r D Q g=D (P g+Q g)
      rw [map_add,hP,hQ]
  | single a p =>
      rw [coefficientDerivative_single]
      by_cases h : a=g
      · subst a; simp
      · simp [AddMonoidAlgebra.single_apply,h]

/-- The lifted oscillator derivative obeys the actual finite Laurent
Leibniz rule. -/
theorem coefficientDerivative_mul (r : ℕ) (D : Derivation ℂ WakFock WakFock)
    (P Q : Auxiliary r) : coefficientDerivative r D (P*Q)=
      coefficientDerivative r D P*Q+P*coefficientDerivative r D Q := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P R hP hR => simp only [add_mul,map_add,hP,hR]; abel
  | single a p =>
      induction Q using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add Q R hQ hR => simp only [mul_add,map_add,hQ,hR]; abel
      | single b q =>
          simp only [single_mul_single,coefficientDerivative_single,D.leibniz,smul_eq_mul,
            ← single_add]
          congr 1
          ring

/-- Oscillator differentiation as a derivation of the actual auxiliary ring. -/
def auxiliaryDerivative (r : ℕ) (D : Derivation ℂ WakFock WakFock) :
    Derivation ℂ (Auxiliary r) (Auxiliary r) where
  toLinearMap := coefficientDerivative r D
  map_one_eq_zero' := by
    rw [AddMonoidAlgebra.one_def,coefficientDerivative_single,D.map_one_eq_zero,
      AddMonoidAlgebra.single_zero]
  leibniz' P Q := by
    rw [coefficientDerivative_mul]
    simp only [smul_eq_mul]
    ring

/-- Applying the auxiliary derivation and selecting a coefficient gives
exactly the original oscillator derivation of that coefficient. -/
theorem auxiliaryDerivative_apply (r : ℕ) (D : Derivation ℂ WakFock WakFock)
    (P : Auxiliary r) (g : Fin r → ℤ) : auxiliaryDerivative r D P g=D (P g) :=
  coefficientDerivative_apply r D P g

/-- A scalar constant times an auxiliary expression is ordinary complex
scalar multiplication, with the repository's polynomial normalization. -/
theorem constant_mul_auxiliary (r : ℕ) (c : ℂ) (P : Auxiliary r) :
    single 0 (MvPolynomial.C c)*P=c • P := by
  ext g : 1
  rw [AddMonoidAlgebra.single_zero_mul_apply]
  change MvPolynomial.C c * P g = c • P g
  rw [MvPolynomial.smul_eq_C_mul]

/-- The nth factorial-normalized term of a finite exponential. -/
def exponentialTerm (r : ℕ) (c : ℂ) (X : Auxiliary r) (n : ℕ) : Auxiliary r :=
  (c^n/(n.factorial : ℂ)) • X^n

/-- The finite exponential through degree N, in scalar-multiplication form. -/
def finiteExponential (r : ℕ) (c : ℂ) (X : Auxiliary r) (N : ℕ) : Auxiliary r :=
  ∑ n∈Finset.range (N+1), exponentialTerm r c X n

/-- The actual screening exponential is this finite factorial sum. -/
theorem exponentialFactor_eq_finiteExponential (r N M m : ℕ) :
    exponentialFactor r N M m=finiteExponential r (-(M : ℂ)/m) (bosonPower r m) N := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  exact constant_mul_auxiliary r _ _

/-- The derivative of a positive factorial term is c times the previous
term times the derivative of X. The factorial coefficient is proved exactly. -/
theorem exponentialTerm_derivative_succ (r : ℕ) (D : Derivation ℂ (Auxiliary r) (Auxiliary r))
    (c : ℂ) (X : Auxiliary r) (n : ℕ) :
    D (exponentialTerm r c X (n+1))=c • (D X*exponentialTerm r c X n) := by
  rw [exponentialTerm,D.map_smul,D.leibniz_pow]
  simp only [Nat.add_sub_cancel,smul_eq_mul] at *
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,exponentialTerm,
    mul_smul_comm,smul_smul,mul_comm (D X)]
  congr 1
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have hn : (n : ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hf : (n.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- The zero factorial term is one. -/
theorem exponentialTerm_zero (r : ℕ) (c : ℂ) (X : Auxiliary r) :
    exponentialTerm r c X 0=1 := by simp [exponentialTerm]

/-- Increasing a finite exponential cutoff adds exactly its new terminal term. -/
theorem finiteExponential_succ (r : ℕ) (c : ℂ) (X : Auxiliary r) (N : ℕ) :
    finiteExponential r c X (N+1)=finiteExponential r c X N+exponentialTerm r c X (N+1) := by
  rw [finiteExponential,Finset.sum_range_succ]
  rfl

/-- Exact finite exponential differentiation WITH its terminal correction.
The correction is retained explicitly until a degree argument can kill its
selected coefficient. This holds for every derivation and every cutoff. -/
theorem finiteExponential_derivative (r : ℕ)
    (D : Derivation ℂ (Auxiliary r) (Auxiliary r)) (c : ℂ) (X : Auxiliary r) (N : ℕ) :
    D (finiteExponential r c X N)+c • (D X*exponentialTerm r c X N)=
      c • (D X*finiteExponential r c X N) := by
  induction N with
  | zero => simp [finiteExponential,exponentialTerm_zero,D.map_one_eq_zero]
  | succ N ih =>
      rw [finiteExponential_succ,map_add,exponentialTerm_derivative_succ]
      rw [ih,mul_add,smul_add]

end
end VOA.Wak.Screening
