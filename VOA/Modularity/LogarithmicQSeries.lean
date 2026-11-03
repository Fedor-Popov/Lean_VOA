/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.PseudoTrace
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Polynomial-valued logarithmic pseudo-trace q-series

For a logarithmic module the nilpotent part of `L₀` contributes
`exp(2πi τ L₀_nil)`.  On a finite projective generalized weight space this exponential is a
finite sum, and applying the Hattori–Stallings pseudo-trace produces a polynomial in `τ`.
Consequently the coefficient carrier for a logarithmic q-series is `ℂ[X]`, not `ℂ`.

This file constructs that coefficient polynomial and assembles a family of such coefficients into
`LogFormalQSeries = ℂ → ℂ[X]`.  Every coefficient is formed from an actual finitely generated
projective module and actual module-linear endomorphisms.  The file deliberately asserts no VOA
origin for those data, no genus-one recursion, no convergence, no spanning theorem, and no
modularity theorem.

The missing VOA-facing layer is an auxiliary algebra action on a `LogVModule` commuting with all
vertex-operator modes, with each generalized weight space finite projective over that algebra.
Miyamoto's generalized-Verma construction is supposed to produce precisely that layer; it is not
currently available in the repository.
-/

namespace VOA

open scoped BigOperators

/-- A formal logarithmic q-series has a polynomial in the logarithmic variable at every complex
exponent. -/
abbrev LogFormalQSeries := ℂ → Polynomial ℂ

/-- The scalar multiplying the `k`-th nilpotent power in `exp(2πi τ N)`. -/
noncomputable def logExpCoeff (k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)

section OnePiece

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable (P : Type*) [AddCommGroup P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
variable [Module.Finite A P] [Module.Projective A P]

/-- The polynomial pseudo-trace of an insertion `S` times the truncated logarithmic exponential
of a nilpotent endomorphism `N`.

At `τ`, this evaluates to the pseudo-trace of
`S · Σ_{k<r} (2πiτ)^k N^k/k!`. -/
noncomputable def pseudoTraceExpPolynomial (phi : symmetricFunctionals ℂ A)
    (S N : Module.End A P) (r : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range r,
    Polynomial.monomial k (logExpCoeff k * pseudoTrace P phi (S * N ^ k))

theorem pseudoTraceExpPolynomial_coeff (phi : symmetricFunctionals ℂ A)
    (S N : Module.End A P) (r k : ℕ) :
    (pseudoTraceExpPolynomial P phi S N r).coeff k =
      if k < r then logExpCoeff k * pseudoTrace P phi (S * N ^ k) else 0 := by
  classical
  simp [pseudoTraceExpPolynomial, Polynomial.coeff_monomial, eq_comm]

/-- Evaluation gives the expected finite pseudo-trace exponential. -/
theorem pseudoTraceExpPolynomial_eval (phi : symmetricFunctionals ℂ A)
    (S N : Module.End A P) (r : ℕ) (tau : ℂ) :
    (pseudoTraceExpPolynomial P phi S N r).eval tau =
      ∑ k ∈ Finset.range r,
        logExpCoeff k * pseudoTrace P phi (S * N ^ k) * tau ^ k := by
  classical
  simp [pseudoTraceExpPolynomial, Polynomial.eval_finsetSum]

/-- Once `N^r = 0`, increasing the cutoff does not change the pseudo-trace polynomial. -/
theorem pseudoTraceExpPolynomial_stable (phi : symmetricFunctionals ℂ A)
    (S N : Module.End A P) {r r' : ℕ} (hrr : r ≤ r') (hN : N ^ r = 0) :
    pseudoTraceExpPolynomial P phi S N r' = pseudoTraceExpPolynomial P phi S N r := by
  classical
  ext k
  rw [pseudoTraceExpPolynomial_coeff, pseudoTraceExpPolynomial_coeff]
  by_cases hkr : k < r
  · rw [if_pos hkr, if_pos (lt_of_lt_of_le hkr hrr)]
  · rw [if_neg hkr]
    by_cases hkr' : k < r'
    · rw [if_pos hkr', pow_eq_zero_of_le (by omega : r ≤ k) hN, mul_zero, map_zero, mul_zero]
    · rw [if_neg hkr']

end OnePiece

section OrdinaryCheck

variable {P : Type*} [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]

/-- With scalar coefficient algebra and zero nilpotent part, the logarithmic pseudo-trace
polynomial is the constant ordinary trace. -/
theorem pseudoTraceExpPolynomial_zero_eq_trace (S : Module.End ℂ P) :
    pseudoTraceExpPolynomial P (idSymmetric ℂ) S 0 1 =
      Polynomial.C (LinearMap.trace ℂ P S) := by
  classical
  rw [pseudoTraceExpPolynomial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one]
  rw [pseudoTrace_idSymmetric_eq_trace]
  simp [logExpCoeff]

end OrdinaryCheck

section Series

universe u

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable (Piece : ℂ → Type u)
variable [∀ e, AddCommGroup (Piece e)] [∀ e, Module A (Piece e)]
variable [∀ e, Module ℂ (Piece e)] [∀ e, IsScalarTower ℂ A (Piece e)]
variable [∀ e, Module.Finite A (Piece e)] [∀ e, Module.Projective A (Piece e)]

/-- Assemble the polynomial pseudo-traces of projective generalized weight pieces into a formal
logarithmic q-series.  The exponent `e` is kept outside the coefficient polynomial, matching the
repository convention `FormalQSeries = ℂ → ℂ`. -/
noncomputable def projectivePseudoTraceQSeries (phi : symmetricFunctionals ℂ A)
    (S N : ∀ e, Module.End A (Piece e)) (cutoff : ℂ → ℕ) : LogFormalQSeries :=
  fun e => pseudoTraceExpPolynomial (Piece e) phi (S e) (N e) (cutoff e)

theorem projectivePseudoTraceQSeries_coeff (phi : symmetricFunctionals ℂ A)
    (S N : ∀ e, Module.End A (Piece e)) (cutoff : ℂ → ℕ) (e : ℂ) (k : ℕ) :
    (projectivePseudoTraceQSeries Piece phi S N cutoff e).coeff k =
      if k < cutoff e then
        logExpCoeff k * pseudoTrace (Piece e) phi (S e * (N e) ^ k)
      else 0 :=
  pseudoTraceExpPolynomial_coeff (Piece e) phi (S e) (N e) (cutoff e) k

/-- Pointwise cutoff-independence for a genuinely nilpotent family. -/
theorem projectivePseudoTraceQSeries_stable (phi : symmetricFunctionals ℂ A)
    (S N : ∀ e, Module.End A (Piece e)) {cutoff cutoff' : ℂ → ℕ}
    (hle : ∀ e, cutoff e ≤ cutoff' e) (hN : ∀ e, (N e) ^ cutoff e = 0) :
    projectivePseudoTraceQSeries Piece phi S N cutoff' =
      projectivePseudoTraceQSeries Piece phi S N cutoff := by
  funext e
  exact pseudoTraceExpPolynomial_stable (Piece e) phi (S e) (N e) (hle e) (hN e)

end Series

end VOA
