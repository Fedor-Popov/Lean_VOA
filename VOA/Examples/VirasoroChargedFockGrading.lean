/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockPositiveOperators

/-!
# Charged Fock grading and positive-mode truncation

The charged zero mode is the oscillator energy plus the scalar vacuum
weight. Its commutator with any positive mode then forces every nonzero
output coefficient to have energy N-n. This coefficient statement also
handles n>N, without truncated subtraction or a fictitious negative grade.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open InverseDS.LeeYangFockVirasoro

/-- The uncharged zero-mode coefficient reads the exact oscillator energy
of that occupation, on every polynomial. -/
theorem fock_zero_coefficient (d : (ℕ × Fin 1) →₀ ℕ) (P : FockN 1) :
    coeff d (LvirN 1 2 0 P) = (Finsupp.weight weightFnN d:ℂ) * coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]
  | monomial e c =>
    rw [LvirN_zero_monomial 1 2 (by norm_num), coeff_smul]
    simp only [smul_eq_mul, coeff_monomial]
    by_cases he : e=d
    · subst e; simp
    · simp [he]

/-- The charged zero mode differs from the uncharged energy operator by
the scalar highest weight p squared minus twice ell p. -/
theorem chargedFock_zero_formula (ell p : ℂ) (P : FockN 1) :
    sectorVirasoro ell p 0 P = LvirN 1 2 0 P + (p^2-2*ell*p) • P := by
  simp [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    alphaMode, smul_smul]
  module

/-- The coefficient version of the actual charged zero-mode action. -/
theorem chargedFock_zero_coefficient (ell p : ℂ) (d : (ℕ × Fin 1) →₀ ℕ)
    (P : FockN 1) :
    coeff d (sectorVirasoro ell p 0 P) =
      ((Finsupp.weight weightFnN d:ℂ)+(p^2-2*ell*p)) * coeff d P := by
  rw [chargedFock_zero_formula, coeff_add, coeff_smul, fock_zero_coefficient]
  simp only [smul_eq_mul]
  ring

/-- A homogeneous Fock polynomial is a zero-mode eigenvector with its
oscillator energy added to the actual scalar highest weight. -/
theorem chargedFock_zero_grade (ell p : ℂ) (N : ℕ) (P : FockN 1)
    (hP : P ∈ gradingWN 1 N) :
    sectorVirasoro ell p 0 P = ((N:ℂ)+(p^2-2*ell*p)) • P := by
  rw [chargedFock_zero_formula, LvirN_zero_gradingWN 1 2 (by norm_num) hP, add_smul]

/-- The actual zero-mode commutator lowers the charged weight by the
integer mode index. The central term vanishes because one index is zero. -/
theorem chargedFock_zero_mode_comm (ell p : ℂ) (n : ℤ) (P : FockN 1) :
    sectorVirasoro ell p 0 (sectorVirasoro ell p n P) -
      sectorVirasoro ell p n (sectorVirasoro ell p 0 P) =
        -(n:ℂ) • sectorVirasoro ell p n P := by
  have h := congrArg (fun f : Module.End ℂ (FockN 1) => f P)
    (sectorVirasoro_virasoro ell p 0 n)
  simpa using h

/-- Outside energy N-n every coefficient of a nonnegative mode applied
to an energy-N polynomial is zero. In particular n>N kills the entire
polynomial; the proof never subtracts natural numbers prematurely. -/
theorem chargedFock_mode_coeff_zero (ell p : ℂ) (n N : ℕ) (P : FockN 1)
    (hP : P ∈ gradingWN 1 N) (d : (ℕ × Fin 1) →₀ ℕ)
    (hd : Finsupp.weight weightFnN d + n ≠ N) :
    coeff d (sectorVirasoro ell p n P) = 0 := by
  have h := chargedFock_zero_mode_comm ell p n P
  rw [chargedFock_zero_grade ell p N P hP, map_smul] at h
  have hc := congrArg (coeff d) h
  rw [coeff_sub, coeff_smul, coeff_smul, chargedFock_zero_coefficient] at hc
  simp only [smul_eq_mul] at hc
  have hm : (((Finsupp.weight weightFnN d:ℂ)+(n:ℂ))-(N:ℂ)) *
      coeff d (sectorVirasoro ell p n P) = 0 := by
    push_cast at hc
    linear_combination hc
  apply (mul_eq_zero.mp hm).resolve_left
  intro he
  apply hd
  have heq := sub_eq_zero.mp he
  exact_mod_cast heq

end VOA.VirasoroScreening
