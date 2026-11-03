/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningAuxiliaryEuler

/-!
# Auxiliary differentiation of the actual finite boson exponential

Euler differentiation produces the finite boson creation series times the
exponential, up to explicitly controlled terminal terms. The whole product
inherits the same cutoff bound by finite Leibniz.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- The finite boson creation series in a single auxiliary variable. -/
def bosonAuxiliarySeries (r N : ℕ) (i : Fin r) : Auxiliary r :=
  ∑ j∈Finset.range N, single (((j+1 : ℕ) : ℤ) • unitExponent r i) (X (2,j))

/-- Auxiliary differentiation of one finite exponential, with its exact
terminal term retained. The mode denominator cancels using m>0. -/
theorem auxiliaryEuler_exponentialFactor (r N M m : ℕ) (hm : 0<m) (i : Fin r) :
    auxiliaryEuler i (exponentialFactor r N M m)+
      (-(M : ℂ)) • ((single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r)*
        exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) N)=
      (-(M : ℂ)) • ((single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r)*
        exponentialFactor r N M m) := by
  have h := finiteExponential_derivative r (auxiliaryEuler i)
    (-(M : ℂ)/m) (bosonPower r m) N
  rw [auxiliaryEuler_bosonPower,smul_mul_assoc,smul_smul,
    smul_mul_assoc,smul_smul] at h
  have hm' : (m : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hc : (-(M : ℂ)/m)*(m : ℂ)=-(M : ℂ) := by field_simp
  rw [hc,← exponentialFactor_eq_finiteExponential] at h
  exact h

/-- The actual terminal Euler correction has auxiliary degree at least
m(N+1), including its extra single-variable boson monomial. -/
theorem auxiliaryEuler_exponential_error_lower (r N M m : ℕ) (i : Fin r) :
    LowerDegree ((m : ℤ)*(N+1))
      ((-(M : ℂ)) • ((single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r)*
        exponentialTerm r (-(M : ℂ)/m) (bosonPower r m) N)) := by
  have ht : LowerDegree (m : ℤ)
      (single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r) :=
    LowerDegree.single r _ _ _ (by rw [exponentDegree_smul_unit])
  have h := (ht.mul (exponentialTerm_boson_lower r M m N)).smul (-(M : ℂ))
  convert h using 1 <;> ring

/-- Each actual positive-mode exponential has its Euler multiplier
modulo an error above the cutoff, with no terminal term discarded by fiat. -/
theorem auxiliaryEuler_exponential_error (r N M m : ℕ) (hm : 0<m) (i : Fin r) :
    LowerDegree (N+1 : ℤ)
      (auxiliaryEuler i (exponentialFactor r N M m)-
        ((-(M : ℂ)) • (single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r))*
          exponentialFactor r N M m) := by
  have he := auxiliaryEuler_exponentialFactor r N M m hm i
  have hl := (auxiliaryEuler_exponential_error_lower r N M m i).neg
  have hh : (N : ℤ)+1≤(m : ℤ)*(N+1) := by
    have hm' : (1 : ℤ)≤m := by omega
    have hn' : (0 : ℤ)≤N := by positivity
    nlinarith
  convert hl.mono hh using 1
  rw [smul_mul_assoc]
  linear_combination he

/-- The whole finite boson exponential product has Euler multiplier
-M times the actual boson creation series, modulo an error above N. -/
theorem auxiliaryEuler_exponential_product_error (r N M : ℕ) (i : Fin r) :
    LowerDegree (N+1 : ℤ)
      (auxiliaryEuler i (∏ j∈Finset.range N,exponentialFactor r N M (j+1))-
        ((-(M : ℂ)) • bosonAuxiliarySeries r N i)*
          (∏ j∈Finset.range N,exponentialFactor r N M (j+1))) := by
  have h := derivative_error_prod (auxiliaryEuler i) (N+1 : ℤ) (Finset.range N)
    (fun j => exponentialFactor r N M (j+1))
    (fun j => (-(M : ℂ)) • (single (((j+1 : ℕ) : ℤ) • unitExponent r i) (X (2,j)) : Auxiliary r))
    (fun j _ => exponentialFactor_lower r N M (j+1)) (by
      intro j hj
      simpa only [Nat.add_sub_cancel] using auxiliaryEuler_exponential_error r N M (j+1) (by omega) i)
  simpa only [← Finset.smul_sum,bosonAuxiliarySeries] using h

end
end VOA.Wak.Screening
