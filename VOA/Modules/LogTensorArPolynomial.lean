/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.LiRegularExp
import Mathlib.Algebra.Polynomial.Roots

/-! # Finite polynomial coefficient tools for the full logarithmic A-formula -/
namespace VOA.LogTensor.Ar
open scoped BigOperators
noncomputable section

/-- The scalar finite coefficient polynomial. -/
def coefficientPolynomial (f : ℕ → ℂ) (K : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range K, Polynomial.C (f k) * Polynomial.X ^ k

@[simp] theorem coefficientPolynomial_eval (f : ℕ → ℂ) (K : ℕ) (z : ℂ) :
    (coefficientPolynomial f K).eval z = ∑ k ∈ Finset.range K, f k*z^k := by
  simp only [coefficientPolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]

theorem coefficientPolynomial_coeff (f : ℕ → ℂ) (K : ℕ)
    (hf : ∀ k, K ≤ k → f k=0) (k : ℕ) : (coefficientPolynomial f K).coeff k = f k := by
  classical
  simp only [coefficientPolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k<K
  · simp [Finset.mem_range.mpr hk]
  · simp [Finset.mem_range,not_lt.mp hk,hf k (not_lt.mp hk)]

/-- Equality at every scalar logarithm value forces equality of every finite coefficient. -/
theorem finite_coefficient_ext (f g : ℕ → ℂ) (K L : ℕ)
    (hf : ∀ k, K ≤ k → f k=0) (hg : ∀ k, L ≤ k → g k=0)
    (h : ∀ z : ℂ, (∑ k ∈ Finset.range K, f k*z^k) = ∑ k ∈ Finset.range L, g k*z^k) : f=g := by
  haveI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n:ℂ)) Nat.cast_injective
  have hp : coefficientPolynomial f K=coefficientPolynomial g L := by
    apply Polynomial.funext
    intro z
    simpa only [coefficientPolynomial_eval] using h z
  funext k
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff k) hp
  simpa only [coefficientPolynomial_coeff f K hf,coefficientPolynomial_coeff g L hg] using hc

/-- The finite FHL logarithm convolution evaluates as inverse log substitution
and the actual first-state nilpotent exponential coefficient polynomial. -/
theorem finite_log_convolution (c z : ℂ) (g : ℕ → ℕ → ℂ) (P Q : ℕ)
    (hP : ∀ l q, P ≤ l → g l q=0) (hQ : ∀ l q, Q ≤ q → g l q=0) :
    (∑ k ∈ Finset.range (P+Q), z^k *
      ∑ l ∈ Finset.range (k+1), (c^l/(l.factorial:ℂ)) * (-1:ℂ)^(k-l) * g l (k-l)) =
    ∑ l ∈ Finset.range P, ((c*z)^l/(l.factorial:ℂ)) * ∑ q ∈ Finset.range Q, (-z)^q*g l q := by
  classical
  have hterms : ∀ k ∈ Finset.range (P+Q), z^k *
      (∑ l ∈ Finset.range (k+1), (c^l/(l.factorial:ℂ)) * (-1:ℂ)^(k-l) * g l (k-l)) =
      ∑ l ∈ Finset.range (k+1), ((c*z)^l/(l.factorial:ℂ)) * (-z)^(k-l)*g l (k-l) := by
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l≤k := by have := Finset.mem_range.mp hl; omega
    have hpow : z^k=z^l*z^(k-l) := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    simp only [show -z=(-1:ℂ)*z by ring,mul_pow,div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hterms]
  have htri := VOA.Huang.LiRegular.tri_reindex (P+Q)
    (fun l q => ((c*z)^l/(l.factorial:ℂ)) * (-z)^q*g l q)
  rw [htri]
  have houter : (∑ l ∈ Finset.range (P+Q),
      ∑ q ∈ Finset.range (P+Q-l), ((c*z)^l/(l.factorial:ℂ)) * (-z)^q*g l q) =
      ∑ l ∈ Finset.range P,
      ∑ q ∈ Finset.range (P+Q-l), ((c*z)^l/(l.factorial:ℂ)) * (-z)^q*g l q := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l hl hln
    apply Finset.sum_eq_zero
    intro q hq
    rw [hP l q (by have := Finset.mem_range.not.mp hln; omega),mul_zero]
  rw [houter]
  apply Finset.sum_congr rfl
  intro l hl
  have hlP : l<P := Finset.mem_range.mp hl
  rw [Finset.mul_sum]
  simp only [← mul_assoc]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro q hq hqn
  rw [hQ l q (by have := Finset.mem_range.not.mp hqn; omega),mul_zero]

end
end VOA.LogTensor.Ar
