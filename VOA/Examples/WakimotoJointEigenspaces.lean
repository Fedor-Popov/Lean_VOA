/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoJointFockSpace

/-!
# Actual energy-charge eigenspaces and joint monomial coefficients

Coefficientwise Euler identities identify the finite occupation subspaces
with the actual simultaneous energy and ghost-charge eigenspaces. In
particular the nonzero screening singular state lies in the finite space
used for the forthcoming ordinary Gram matrix argument.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open scoped BigOperators
noncomputable section

/-- An oscillator power is an actual weighted Euler eigenvector. -/
theorem Eul_X_power (w : Fin 3×ℕ→ℂ) (v : Fin 3×ℕ) (n : ℕ) :
    Eul w ((X v : WakFock)^n)=((n : ℂ)*w v) • ((X v : WakFock)^n) := by
  induction n with
  | zero => simp [Eul_one']
  | succ n ih =>
      rw [pow_succ,Eul_mul,ih,Eul_X]
      simp only [Nat.cast_add,Nat.cast_one,smul_eq_C_mul,map_mul,map_add,map_one]
      ring

/-- An actual monomial is an Euler eigenvector with the sum of its
oscillator weights, including any signed weight assignment. -/
theorem Eul_monomial_one (w : Fin 3×ℕ→ℂ) (d : Occupation) :
    Eul w (monomial d (1 : ℂ))=Finsupp.weight w d • monomial d (1 : ℂ) := by
  induction d using Finsupp.induction_linear with
  | zero => simp [monomial_zero,Eul_C',Eul_one']
  | add d e hd he =>
      rw [show monomial (d+e) (1 : ℂ)=monomial d 1*monomial e 1 by simp,
        Eul_mul,hd,he,map_add,add_smul]
      simp only [smul_mul_assoc,mul_smul_comm]
  | single v n =>
      rw [← X_pow_eq_monomial,Finsupp.weight_single,Eul_X_power]
      simp [nsmul_eq_mul]

/-- Weighted Euler differentiation multiplies every actual polynomial
coefficient by the corresponding occupation weight. -/
theorem coeff_Eul (w : Fin 3×ℕ→ℂ) (d : Occupation) (P : WakFock) :
    coeff d (Eul w P)=Finsupp.weight w d*coeff d P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,coeff_add,hP,hQ,mul_add]
  | monomial e z =>
      have hz : monomial e z=z • (monomial e (1 : ℂ)) := by rw [smul_monomial]; simp only [smul_eq_mul,mul_one]
      rw [hz,map_smul,Eul_monomial_one,coeff_smul,coeff_smul,coeff_smul]
      by_cases he : d=e
      · subst e; simp [smul_eq_mul]; ring
      · simp [coeff_monomial,he,Ne.symm he]

/-- Complex Euler energy is the natural occupation energy embedded in C. -/
theorem weight_wtFn (d : Occupation) : Finsupp.weight wtFn d=(occupationEnergy d : ℂ) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => rw [map_add,map_add,Nat.cast_add,hd,he]
  | single v n =>
      simp only [occupationEnergy,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_mul]
      congr 1
      simp [wtFn,oscillatorEnergy]

/-- Complex Euler charge is the integer occupation charge embedded in C. -/
theorem weight_chFn (d : Occupation) : Finsupp.weight chFn d=(occupationCharge d : ℂ) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => rw [map_add,map_add,Int.cast_add,hd,he]
  | single v n =>
      simp only [occupationCharge,Finsupp.weight_single,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
      congr 1
      simp [chFn,oscillatorCharge]

/-- Actual simultaneous Euler eigenvectors have exactly the prescribed
joint monomial support. -/
theorem mem_jointFockSpace_of_eigen (n : ℕ) (c : ℤ) (P : WakFock)
    (hE : Dwt P=(n : ℂ) • P) (hC : Dch P=(c : ℂ) • P) :
    P∈jointFockSpace n c := by
  change (P.support : Set Occupation)⊆{d : Occupation | occupationEnergy d=n ∧ occupationCharge d=c}
  intro d hd
  have hd' : coeff d P≠0 := mem_support_iff.mp hd
  have he := congrArg (coeff d) hE
  have hc := congrArg (coeff d) hC
  rw [Dwt,coeff_Eul,weight_wtFn,coeff_smul] at he
  rw [Dch,coeff_Eul,weight_chFn,coeff_smul] at hc
  constructor
  · exact_mod_cast (mul_right_cancel₀ hd' he)
  · exact_mod_cast (mul_right_cancel₀ hd' hc)

/-- Every polynomial supported at one joint label is an actual simultaneous
energy and charge eigenvector. -/
theorem jointFockSpace_eigen (n : ℕ) (c : ℤ) (P : WakFock)
    (hP : P∈jointFockSpace n c) : Dwt P=(n : ℂ) • P ∧ Dch P=(c : ℂ) • P := by
  have hs : (P.support : Set Occupation)⊆{d : Occupation | occupationEnergy d=n ∧ occupationCharge d=c} := hP
  constructor
  · ext d
    rw [Dwt,coeff_Eul,weight_wtFn,coeff_smul]
    by_cases hd : coeff d P=0
    · simp [hd]
    · rw [(hs (mem_support_iff.mpr hd)).1]; rfl
  · ext d
    rw [Dch,coeff_Eul,weight_chFn,coeff_smul]
    by_cases hd : coeff d P=0
    · simp [hd]
    · rw [(hs (mem_support_iff.mpr hd)).2]; rfl

/-- The finite screening state belongs to its ACTUAL finite joint
occupation space. This is used with nonvanishing, not merely formal degree. -/
theorem screening_mem_jointFockSpace (r q M : ℕ) (hq : 0<q) :
    Screening.state r q M∈jointFockSpace (r*q) (r : ℤ) := by
  apply mem_jointFockSpace_of_eigen
  · simpa only [Nat.cast_mul] using Screening.state_energy r q M hq
  · simpa only [Int.cast_natCast] using Screening.state_charge r q M

end
end VOA.Wak.Charged
