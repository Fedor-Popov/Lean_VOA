/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalPowerRadical

/-!
# First variation of the horizontal pairing

At weight d every reflected horizontal descendant is radical. Therefore a first
pairing coefficient ignores derivatives of coefficients in the right word
expression. Constant creation coordinates identify this coefficient with
a genuine linear functional on the actual weight-d Verma module.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Polynomial HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter adjointWord)
noncomputable section

/-- The actual polynomial pairing of a fixed horizontal descendant with
an arbitrary current word, retaining the highest-weight variable. -/
def reflectionPairPolynomial (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X+Polynomial.C (d : ℂ)]
    (wordPolynomial (adjointWord ((u++List.replicate (d+1) (1,0)).map lowerLetter)++w))

/-- Polynomial evaluation agrees with the actual normalized Verma form
for every highest weight, including the singular value d. -/
theorem reflectionPairPolynomial_eval (k h : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    (reflectionPairPolynomial k d u w).eval h=
      contravariant k (h+(d : ℂ)) (indexedWord k (h+(d : ℂ)) (u++List.replicate (d+1) (1,0)))
        (currentWord (mode k (h+(d : ℂ))) w (highestVector k (h+(d : ℂ)))) := by
  rw [indexedWord,contravariant_wordPolynomial]
  unfold reflectionPairPolynomial
  change Polynomial.evalRingHom h (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X+Polynomial.C (d : ℂ)] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom h).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom h (![Polynomial.C k,X+Polynomial.C (d : ℂ)] a))=![k,h+(d : ℂ)] := by
    funext a
    fin_cases a <;> simp
  rw [hx]
  rfl

/-- Every horizontal pairing has zero constant term, by the actual
radical theorem; the right word need not be a creation word. -/
theorem reflectionPairPolynomial_zero (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    (reflectionPairPolynomial k d u w).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero,reflectionPairPolynomial_eval]
  rw [show (0 : ℂ) + (d : ℂ) = (d : ℂ) from zero_add _]
  rw [← horizontalReflection_indexedWord,horizontalReflection_radical]
  rfl

/-- Extend the first pairing coefficient on actual PBW vectors linearly.
Uniform creation coordinates will prove the same rule on unsorted words. -/
def reflectionTangentRow (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) : Module.Dual ℂ (Verma k d) :=
  (occupationBasis k d).constr ℂ
    (fun e => (reflectionPairPolynomial k d u (occupationWord e)).coeff 1)

/-- On the actual occupation basis the tangent row has its prescribed
first polynomial coefficient. -/
theorem reflectionTangentRow_basis (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (e : Occupation) :
    reflectionTangentRow k d u (occupationBasis k d e)=
      (reflectionPairPolynomial k d u (occupationWord e)).coeff 1 :=
  (occupationBasis k d).constr_basis ℂ _ e

/-- On any indexed creation word the tangent row is the first polynomial
coefficient, with no derivative of a basis-change matrix. -/
theorem reflectionTangentRow_indexed (k : ℂ) (d : ℕ) (u w : List (Fin 3×ℕ)) :
    reflectionTangentRow k d u (indexedWord k d w)=
      (reflectionPairPolynomial k d u (w.map lowerLetter)).coeff 1 := by
  let a := (occupationBasis k d).repr (indexedWord k d w)
  have hp : reflectionPairPolynomial k d u (w.map lowerLetter)=
      ∑j∈a.support,Polynomial.C (a j)*reflectionPairPolynomial k d u (occupationWord j) := by
    apply Polynomial.funext
    intro h
    simp only [eval_finsetSum,eval_mul,eval_C,reflectionPairPolynomial_eval]
    have hc : (occupationBasis k (h+(d : ℂ))).repr (indexedWord k (h+(d : ℂ)) w)=a :=
      indexedWord_coordinates_independent k (h+(d : ℂ)) k d w
    have he := (occupationBasis k (h+(d : ℂ))).linearCombination_repr (indexedWord k (h+(d : ℂ)) w)
    rw [hc] at he
    change contravariant k (h+(d : ℂ)) _ (indexedWord k (h+(d : ℂ)) w)=_
    rw [← he]
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
      occupationBasis_apply,smul_eq_mul]
  rw [hp,finsetSum_coeff]
  have he := congrArg (reflectionTangentRow k d u)
    ((occupationBasis k d).linearCombination_repr (indexedWord k d w))
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    reflectionTangentRow_basis,smul_eq_mul] at he
  simpa only [coeff_C_mul] using he.symm

/-- The tangent rule also holds for literal creation letters, including
F_0, without choosing or changing their order. -/
theorem reflectionTangentRow_lower (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ))
    (w : List (Fin 3×ℤ)) (hw : ∀an∈w,IsLower an.1 an.2) :
    reflectionTangentRow k d u (currentWord (mode k d) w (highestVector k d))=
      (reflectionPairPolynomial k d u w).coeff 1 := by
  rw [← lower_word_indexed k d w hw,reflectionTangentRow_indexed]
  have he : (w.map lowerIndex).map lowerLetter=w := by
    rw [List.map_map]
    induction w with
    | nil => rfl
    | cons an w ih =>
      simp only [List.map_cons,Function.comp_apply]
      rw [lowerLetter_lowerIndex an (hw an (by simp)),ih (fun bn hb => hw bn (by simp [hb]))]
  rw [he]

/-- Pair a horizontal word with a finite normal expression, retaining both
scalar powers and their complete highest-weight dependence. -/
def reflectionNormalPair (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) : NormalForm→ₗ[ℂ]ℂ[X] :=
  Finsupp.linearCombination ℂ (fun t =>
    Polynomial.C (k^t.1)*(X+Polynomial.C (d : ℂ))^t.2.1*reflectionPairPolynomial k d u t.2.2)

/-- Evaluation of the normal-expression pairing is its actual bilinear
pairing in the corresponding Verma module. -/
theorem reflectionNormalPair_eval (k h : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (f : NormalForm) :
    (reflectionNormalPair k d u f).eval h=
      contravariant k (h+(d : ℂ)) (indexedWord k (h+(d : ℂ)) (u++List.replicate (d+1) (1,0)))
        (HighestNormalOrdering.evaluate (mode k (h+(d : ℂ))) k (h+(d : ℂ)) (highestVector k (h+(d : ℂ))) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,eval_add,ihf,ihg]
  | single t z =>
    rw [reflectionNormalPair,Finsupp.linearCombination_single,evaluate_single]
    simp only [eval_smul,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_C,
      reflectionPairPolynomial_eval,map_smul,smul_eq_mul]

/-- Radical cancellation removes every derivative of a right normal
coefficient. Only the actual value of that expression at weight d survives. -/
theorem reflectionTangentRow_normal (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ))
    (f : NormalForm) (hf : f∈lowerForms) :
    (reflectionNormalPair k d u f).coeff 1=
      reflectionTangentRow k d u
        (HighestNormalOrdering.evaluate (mode k d) k d (highestVector k d) f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    rw [reflectionNormalPair,Finsupp.linearCombination_single,one_smul,
      evaluate_single,one_smul,map_smul,reflectionTangentRow_lower k d u _ ht]
    rw [Polynomial.mul_coeff_one,reflectionPairPolynomial_zero,mul_zero,add_zero]
    simp [smul_eq_mul,coeff_zero_eq_eval_zero]
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,coeff_add,ihf,ihg]
  | smul z f hf ih => simp only [map_smul,coeff_smul,ih]

/-- The first coefficient of a horizontal pairing depends only on the
actual right-hand state at weight d, even for words with positive modes. -/
theorem reflectionTangentRow_word (k : ℂ) (d : ℕ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    reflectionTangentRow k d u (currentWord (mode k d) w (highestVector k d))=
      (reflectionPairPolynomial k d u w).coeff 1 := by
  have hp : reflectionPairPolynomial k d u w=reflectionNormalPair k d u (wordNormal w) := by
    apply Polynomial.funext
    intro h
    rw [reflectionPairPolynomial_eval,reflectionNormalPair_eval,
      evaluate_wordNormal (mode k (h+(d : ℂ))) k (h+(d : ℂ)) (highestVector k (h+(d : ℂ))) (mode_comm k (h+(d : ℂ))) (mode_highest k (h+(d : ℂ)))]
  rw [hp,reflectionTangentRow_normal k d u _ (wordNormal_mem_lowerForms w),
    evaluate_wordNormal (mode k d) k d (highestVector k d) (mode_comm k d) (mode_highest k d)]

end
end VOA.AffineVOA.HighestModule
