/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningLoweringPositive

/-!
# Actual auxiliary Euler differentiation and coefficient integration by parts

These operators differentiate the auxiliary Laurent variables while keeping
Wakimoto oscillator coefficients fixed. Their selected-coefficient identity
is finite algebraic integration by parts, with signed integer exponents.
-/
namespace VOA.Wak.Screening
open AddMonoidAlgebra VirasoroScreening MvPolynomial
open scoped BigOperators
noncomputable section

/-- Euler differentiation in auxiliary variable i, with actual oscillator
coefficients. Negative exponents remain signed integers. -/
def auxiliaryEulerLinear {r : ℕ} (i : Fin r) : Auxiliary r →ₗ[ℂ] Auxiliary r :=
  Finsupp.lsum ℂ (fun g => (g i : ℂ) • Finsupp.lsingle g)

/-- A single Laurent monomial is an Euler eigenvector with its signed
exponent; the actual oscillator coefficient is only scalar multiplied. -/
theorem auxiliaryEulerLinear_single {r : ℕ} (i : Fin r) (g : Fin r → ℤ) (P : WakFock) :
    auxiliaryEulerLinear i (single g P)=single g ((g i : ℂ) • P) := by
  change (Finsupp.lsum ℂ (fun g : Fin r → ℤ => (g i : ℂ) • Finsupp.lsingle g))
    (Finsupp.single g P)=_
  rw [Finsupp.lsum_single]
  change (g i : ℂ) • (Finsupp.single g P : (Fin r → ℤ) →₀ WakFock)=_
  exact Finsupp.smul_single _ _ _

/-- Euler differentiation acts on each actual coefficient by its exponent. -/
theorem auxiliaryEulerLinear_apply {r : ℕ} (i : Fin r) (P : Auxiliary r)
    (g : Fin r → ℤ) : auxiliaryEulerLinear i P g=(g i : ℂ) • P g := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; change (0 : WakFock)=_ • 0; rw [smul_zero]
  | add P Q hP hQ =>
      rw [map_add]
      change auxiliaryEulerLinear i P g+auxiliaryEulerLinear i Q g=_ • (P g+Q g)
      rw [hP,hQ,smul_add]
  | single a p =>
      rw [auxiliaryEulerLinear_single]
      by_cases h : a=g
      · subst a; simp
      · simp [AddMonoidAlgebra.single_apply,h]

/-- Actual auxiliary Euler differentiation satisfies the finite Laurent
product rule, independently of oscillator variables. -/
theorem auxiliaryEulerLinear_mul {r : ℕ} (i : Fin r) (P Q : Auxiliary r) :
    auxiliaryEulerLinear i (P*Q)=auxiliaryEulerLinear i P*Q+P*auxiliaryEulerLinear i Q := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P R hP hR => simp only [add_mul,map_add,hP,hR]; abel
  | single a p =>
      induction Q using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add Q R hQ hR => simp only [mul_add,map_add,hQ,hR]; abel
      | single b q =>
          simp only [single_mul_single,auxiliaryEulerLinear_single,Pi.add_apply,
            Int.cast_add,add_smul,smul_mul_assoc,mul_smul_comm,← single_add]

/-- The auxiliary Euler operator as a genuine complex derivation. -/
def auxiliaryEuler {r : ℕ} (i : Fin r) : Derivation ℂ (Auxiliary r) (Auxiliary r) where
  toLinearMap := auxiliaryEulerLinear i
  map_one_eq_zero' := by
    rw [AddMonoidAlgebra.one_def,auxiliaryEulerLinear_single]
    simp
    rfl
  leibniz' P Q := by
    rw [auxiliaryEulerLinear_mul]
    simp only [smul_eq_mul]
    ring

/-- The bundled auxiliary derivative has the same exact coefficient formula. -/
theorem auxiliaryEuler_apply {r : ℕ} (i : Fin r) (P : Auxiliary r) (g : Fin r → ℤ) :
    auxiliaryEuler i P g=(g i : ℂ) • P g := auxiliaryEulerLinear_apply i P g

/-- Its action on a Laurent monomial leaves the oscillator coefficient
unchanged apart from multiplication by the signed exponent. -/
theorem auxiliaryEuler_single {r : ℕ} (i : Fin r) (g : Fin r → ℤ) (P : WakFock) :
    auxiliaryEuler i (single g P)=single g ((g i : ℂ) • P) := auxiliaryEulerLinear_single i g P

/-- Exact finite integration by parts at the selected common exponent:
the Euler derivative minus L times the expression has zero selected
coefficient, without an analytic contour or an infinite series. -/
theorem auxiliaryEuler_selected_zero (r q M : ℕ) (i : Fin r) (P : Auxiliary r) :
    (auxiliaryEuler i P-((((r-1)*M+q-1 : ℕ) : ℂ) • P))
      (fun _ => (((r-1)*M+q-1 : ℕ) : ℤ))=0 := by
  change (auxiliaryEuler i P) _-(((r-1)*M+q-1 : ℕ) : ℂ) • P _=0
  rw [auxiliaryEuler_apply]
  simp only [Int.cast_natCast,sub_self]

/-- Auxiliary differentiation in i kills a beta factor involving a
different auxiliary variable j. -/
theorem auxiliaryEuler_betaFactor_ne (r D : ℕ) (i j : Fin r) (hij : i≠j) :
    auxiliaryEuler i (betaFactor r D j)=0 := by
  simp only [betaFactor,map_sum,auxiliaryEuler_single]
  apply Finset.sum_eq_zero
  intro n hn
  simp [unitExponent,Pi.single_eq_of_ne hij]
  rfl

/-- In differentiating an integrand with beta factor i omitted, every
remaining beta factor is constant with respect to auxiliary variable i. -/
theorem auxiliaryEuler_beta_omitted (r D : ℕ) (i : Fin r) :
    auxiliaryEuler i (∏ j∈Finset.univ.erase i,betaFactor r D j)=0 := by
  classical
  apply derivative_prod_zero
  intro j hj
  exact auxiliaryEuler_betaFactor_ne r D i j (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Euler differentiation of the m-th boson power singles out the i-th
auxiliary monomial, multiplied by its positive mode index. -/
theorem auxiliaryEuler_bosonPower (r m : ℕ) (i : Fin r) :
    auxiliaryEuler i (bosonPower r m)=
      (m : ℂ) • (single ((m : ℤ) • unitExponent r i) (X (2,m-1)) : Auxiliary r) := by
  classical
  simp only [bosonPower,map_sum,auxiliaryEuler_single]
  rw [Finset.sum_eq_single i]
  · simp [unitExponent,← Finsupp.smul_single]
  · intro j hj hji
    simp [unitExponent,Pi.single_eq_of_ne (Ne.symm hji)]
    rfl
  · simp

end
end VOA.Wak.Screening
