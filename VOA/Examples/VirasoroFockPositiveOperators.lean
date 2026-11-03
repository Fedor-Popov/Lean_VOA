/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaNonvanishing

/-!
# Actual positive Fock modes as finite differential operators

The positive modes are identified on the existing polynomial carrier using
the proved oscillator commutator and induction on polynomials. The first
mode is a derivation; the second is a derivation plus the square of the
first oscillator derivative. Thus no infinite Sugawara sum has to be
reinterpreted as an unproved differential formula.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open InverseDS.LeeYangFockVirasoro InverseDS.VirasoroVerma

/-- The energy-lowering polynomial derivation: an oscillator of energy k
is sent to k times the oscillator of energy k-n, if that energy is positive. -/
noncomputable def fockShiftDerivation (n : ℕ) : Derivation ℂ (FockN 1) (FockN 1) :=
  MvPolynomial.mkDerivation ℂ (fun v : ℕ × Fin 1 =>
    if n ≤ v.1 then ((v.1+1:ℕ):ℂ) • X (v.1-n, v.2) else 0)

/-- The defining action of the shift derivation on one oscillator. -/
theorem fockShiftDerivation_X (n i : ℕ) (a : Fin 1) :
    fockShiftDerivation n (X (i,a)) =
      if n ≤ i then ((i+1:ℕ):ℂ) • X (i-n,a) else 0 := by
  simp [fockShiftDerivation]

/-- Move an actual Sugawara mode through multiplication by any rank-one
oscillator. This is the already proved Virasoro-current commutator evaluated
on an arbitrary polynomial, including all possible signs of the output mode. -/
theorem fockLvir_mul_X (n : ℤ) (i : ℕ) (P : FockN 1) :
    LvirN 1 2 n (X (i,0)*P) =
      ((i+1:ℕ):ℂ) • oscN 1 2 0 (n-(i:ℤ)-1) P + X (i,0)*LvirN 1 2 n P := by
  have h := LvirN_oscN 1 2 (by norm_num) 0 n (-(i:ℤ)-1) P
  have hi : -((i:ℤ))-1 < 0 := by omega
  rw [oscN_apply_neg 1 2 0 hi, oscN_apply_neg 1 2 0 hi] at h
  have he : (-(-(i:ℤ)-1)-1).toNat = i := by omega
  rw [he] at h
  convert h using 1 <;> push_cast <;> congr 1 <;> ring

/-- The actual first Sugawara mode satisfies the same variable-multiplication
rule as the energy-lowering derivation. -/
theorem fockLvir_one_mul_X (i : ℕ) (P : FockN 1) :
    LvirN 1 2 1 (X (i,0)*P) =
      fockShiftDerivation 1 (X (i,0))*P + X (i,0)*LvirN 1 2 1 P := by
  rw [fockLvir_mul_X, fockShiftDerivation_X]
  by_cases hi : i=0
  · subst i
    simp
  · have hin : (1:ℤ)-(i:ℤ)-1 < 0 := by omega
    rw [oscN_apply_neg 1 2 0 hin, if_pos (by omega)]
    have he : (-((1:ℤ)-(i:ℤ)-1)-1).toNat = i-1 := by omega
    rw [he, smul_mul_assoc]

/-- The actual first Sugawara mode is the shift derivation on every Fock
polynomial, not merely on a proposed screening state. -/
theorem fockLvir_one (P : FockN 1) :
    LvirN 1 2 1 P = fockShiftDerivation 1 P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.C_eq_smul_one, map_smul]
    have hv : LvirN 1 2 1 (1 : FockN 1) = 0 := LvirN_vacuum 1 2 (by norm_num)
    simp [hv]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    rcases v with ⟨i,a⟩
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    rw [mul_comm P (X (i,0)), fockLvir_one_mul_X, hP,
      (fockShiftDerivation 1).leibniz]
    simp only [smul_eq_mul]
    ring

/-- Applying the first oscillator derivative twice to a variable times P
produces exactly twice the first derivative when that variable is X_0. -/
theorem fock_second_derivative_mul_X (i : ℕ) (P : FockN 1) :
    pderiv (0,0) (pderiv (0,0) (X (i,0)*P)) =
      X (i,0)*pderiv (0,0) (pderiv (0,0) P) +
        if i=0 then (2:ℂ) • pderiv (0,0) P else 0 := by
  classical
  by_cases hi : i=0
  · subst i
    simp [MvPolynomial.pderiv_mul, two_smul]
    ring
  · simp [MvPolynomial.pderiv_mul, hi, Ne.symm hi]

/-- The actual second Sugawara mode has a shift-derivation term and the
extra second-derivative commutator at the first oscillator. -/
theorem fockLvir_two_mul_X (i : ℕ) (P : FockN 1) :
    LvirN 1 2 2 (X (i,0)*P) =
      fockShiftDerivation 2 (X (i,0))*P + X (i,0)*LvirN 1 2 2 P +
        if i=0 then (2:ℂ) • pderiv (0,0) P else 0 := by
  rw [fockLvir_mul_X, fockShiftDerivation_X]
  rcases i with _ | _ | i
  · norm_num [oscN_apply_pos 1 2 0 (by norm_num : (0:ℤ)<1)]
    abel
  · simp
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
    rw [oscN_apply_neg 1 2 0 (by omega : (2:ℤ)-((i+2:ℕ):ℤ)-1 < 0)]
    have he : (-((2:ℤ)-((i+2:ℕ):ℤ)-1)-1).toNat = (i+2)-2 := by omega
    rw [he, smul_mul_assoc]

/-- The actual second Sugawara mode is the second shift derivation plus
one second derivative in X_0, with the normalization fixed by level two. -/
theorem fockLvir_two (P : FockN 1) :
    LvirN 1 2 2 P = fockShiftDerivation 2 P + pderiv (0,0) (pderiv (0,0) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hv : LvirN 1 2 2 (1 : FockN 1) = 0 := LvirN_vacuum 1 2 (by norm_num)
    rw [MvPolynomial.C_eq_smul_one, map_smul]
    simp [hv]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; abel
  | mul_X P v hP =>
    rcases v with ⟨i,a⟩
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    rw [mul_comm P (X (i,0)), fockLvir_two_mul_X, hP,
      (fockShiftDerivation 2).leibniz, fock_second_derivative_mul_X]
    simp only [smul_eq_mul]
    ring

/-- The ACTUAL first charged, background-shifted Virasoro mode on every
polynomial: shift derivation plus 2(p-2ell) times the first derivative. -/
theorem sectorVirasoro_one_differential (ell p : ℂ) (P : FockN 1) :
    sectorVirasoro ell p 1 P = fockShiftDerivation 1 P +
      (2*(p-2*ell)) • pderiv (0,0) P := by
  simp only [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    alphaMode, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
  norm_num [oscN_apply_pos 1 2 0 (by norm_num : (0:ℤ)<1), fockLvir_one]
  module

/-- The ACTUAL second charged Virasoro mode: shift derivation, one second
X_0 derivative, and 4(p-3ell) times the X_1 derivative. -/
theorem sectorVirasoro_two_differential (ell p : ℂ) (P : FockN 1) :
    sectorVirasoro ell p 2 P = fockShiftDerivation 2 P +
      pderiv (0,0) (pderiv (0,0) P) + (4*(p-3*ell)) • pderiv (1,0) P := by
  simp only [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    alphaMode, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
  norm_num [oscN_apply_pos 1 2 0 (by norm_num : (0:ℤ)<2), fockLvir_two]
  module

end VOA.VirasoroScreening
