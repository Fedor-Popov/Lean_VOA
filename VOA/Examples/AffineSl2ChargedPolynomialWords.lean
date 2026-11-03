/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ChargedPolynomialOperators
import VOA.Examples.AffineSl2HighestWords

/-!
# Highest-weight leading coefficients of actual Fock words

For words without a Cartan zero mode, only lowering-current letters can
contribute a highest-weight power. The top coefficient replaces each such
letter by its gamma oscillator, keeping every other actual current.
-/
namespace VOA.Wak.Charged
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Number of lowering-current letters, the sharp possible highest-weight
power before any cancellations in a literal Fock word. -/
def loweringCount : List (Fin 3×ℤ)→ℕ
  | [] => 0
  | an::w => (if an.1=1 then 1 else 0)+loweringCount w

/-- The operator selected when extracting the maximal possible highest-weight
power. For F it is gamma; the other colours retain their actual constant part. -/
def leadingCurrent (k : ℂ) (a : Fin 3) (n : ℤ) : Module.End ℂ WakFock :=
  if a=1 then Gam n else J k 0 a n

/-- A literal current word acting on a constant Fock vector with highest
weight retained formally. This is a finite polynomial construction. -/
def polynomialWord (k : ℂ) : List (Fin 3×ℤ)→WakFock→FockPolynomial
  | [],P => PolynomialModule.single ℂ 0 P
  | an::w,P => polynomialCurrent k an.1 an.2 (polynomialWord k w P)

/-- Specializing the formal highest weight recovers the full actual word. -/
theorem polynomialWord_eval (k h : ℂ) (w : List (Fin 3×ℤ)) (P : WakFock) :
    PolynomialModule.eval h (polynomialWord k w P)=currentWord (J k h) w P := by
  induction w with
  | nil => simp [polynomialWord,currentWord]
  | cons an w ih => rw [polynomialWord,polynomialCurrent_eval,ih]; rfl

/-- When the Cartan zero mode is excluded, the only linear charge operator
is the gamma term of a lowering letter. -/
theorem chargeLinear_nonzero_mode (a : Fin 3) (n : ℤ) (hn : a=2→n≠0) :
    chargeLinear a n=if a=1 then Gam n else 0 := by
  fin_cases a <;> simp_all [chargeLinear]

/-- The actual word polynomial has degree at most its number of lowering
letters; Cartan zero modes are explicitly excluded. -/
theorem polynomialWord_degree (k : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,an.1=2→an.2≠0) (P : WakFock) :
    FockDegreeLE (loweringCount w) (polynomialWord k w P) := by
  induction w with
  | nil =>
    intro j hj
    simp only [loweringCount,polynomialWord,PolynomialModule.single_apply]
    rw [if_neg (by omega)]
  | cons an w ih =>
    have htail : ∀ bn∈w,bn.1=2→bn.2≠0 := fun bn hb => hw bn (List.mem_cons_of_mem _ hb)
    have hl := chargeLinear_nonzero_mode an.1 an.2 (hw an (by simp))
    simp only [loweringCount,polynomialWord]
    by_cases ha : an.1=1
    · simpa [ha,Nat.add_comm] using polynomialCurrent_degree k an.1 an.2 (ih htail)
    · simp only [ha,ite_false,zero_add]
      exact polynomialCurrent_degree_constant k an.1 an.2 (by simpa [ha] using hl) (ih htail)

/-- The top coefficient equals an actual operator word in which every F
letter is replaced by gamma. It may still vanish; no nonvanishing is assumed. -/
theorem polynomialWord_top (k : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,an.1=2→an.2≠0) (P : WakFock) :
    polynomialWord k w P (loweringCount w)=currentWord (leadingCurrent k) w P := by
  induction w with
  | nil => simp [polynomialWord,loweringCount,currentWord,PolynomialModule.single_apply]
  | cons an w ih =>
    have htail : ∀ bn∈w,bn.1=2→bn.2≠0 := fun bn hb => hw bn (List.mem_cons_of_mem _ hb)
    have hl := chargeLinear_nonzero_mode an.1 an.2 (hw an (by simp))
    have hd := polynomialWord_degree k w htail P
    simp only [polynomialWord,loweringCount,currentWord,Module.End.mul_apply]
    by_cases ha : an.1=1
    · simp only [ha,ite_true,Nat.add_comm 1]
      rw [polynomialCurrent_top k 1 an.2 hd,ih htail]
      simp [leadingCurrent,chargeLinear]
    · simp only [ha,ite_false,zero_add]
      rw [polynomialCurrent_top_constant k an.1 an.2 (by simpa [ha] using hl),ih htail]
      simp [leadingCurrent,ha]

/-- Actual creation words have no Cartan zero letter, including when the
horizontal lowering F-zero is present. -/
theorem occupationWord_no_cartan_zero (d : Occupation) :
    ∀ an∈occupationWord d,an.1=2→an.2≠0 := by
  intro an han ha
  have hl := occupationWord_lower d an han
  rcases hl with hneg | ⟨hz,hf⟩
  · omega
  · have : (2 : Fin 3)=1 := ha.symm.trans hf
    exact False.elim (by cases this)

end
end VOA.Wak.Charged
