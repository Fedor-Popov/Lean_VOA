/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HorizontalRadical

/-!
# First variation of the horizontal pairing

At weight zero every horizontal descendant is radical. Therefore a first
pairing coefficient ignores derivatives of coefficients in the right word
expression. Constant creation coordinates identify this coefficient with
a genuine linear functional on the actual weight-zero Verma module.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Polynomial HighestNormalOrdering
open NormalOrdering (currentWord)
open Wak.Charged (Occupation occupationWord lowerLetter adjointWord)
noncomputable section

/-- The actual polynomial pairing of a fixed horizontal descendant with
an arbitrary current word, retaining the highest-weight variable. -/
def horizontalPairPolynomial (k : ℂ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X]
    (wordPolynomial (adjointWord ((u++[(1,0)]).map lowerLetter)++w))

/-- Polynomial evaluation agrees with the actual normalized Verma form
for every highest weight, including the singular value zero. -/
theorem horizontalPairPolynomial_eval (k h : ℂ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    (horizontalPairPolynomial k u w).eval h=
      contravariant k h (indexedWord k h (u++[(1,0)]))
        (currentWord (mode k h) w (highestVector k h)) := by
  rw [indexedWord,contravariant_wordPolynomial]
  unfold horizontalPairPolynomial
  change Polynomial.evalRingHom h (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom h).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom h (![Polynomial.C k,X] a))=![k,h] := by
    funext a
    fin_cases a <;> simp
  rw [hx]
  rfl

/-- Every horizontal pairing has zero constant term, by the actual
radical theorem; the right word need not be a creation word. -/
theorem horizontalPairPolynomial_zero (k : ℂ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    (horizontalPairPolynomial k u w).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero,horizontalPairPolynomial_eval,
    ← horizontalEmbedding_indexedWord,horizontalEmbedding_radical]
  rfl

/-- Extend the first pairing coefficient on actual PBW vectors linearly.
Uniform creation coordinates will prove the same rule on unsorted words. -/
def horizontalTangentRow (k : ℂ) (u : List (Fin 3×ℕ)) : Module.Dual ℂ (Verma k 0) :=
  (occupationBasis k 0).constr ℂ
    (fun d => (horizontalPairPolynomial k u (occupationWord d)).coeff 1)

/-- On the actual occupation basis the tangent row has its prescribed
first polynomial coefficient. -/
theorem horizontalTangentRow_basis (k : ℂ) (u : List (Fin 3×ℕ)) (d : Occupation) :
    horizontalTangentRow k u (occupationBasis k 0 d)=
      (horizontalPairPolynomial k u (occupationWord d)).coeff 1 :=
  (occupationBasis k 0).constr_basis ℂ _ d

/-- On any indexed creation word the tangent row is the first polynomial
coefficient, with no derivative of a basis-change matrix. -/
theorem horizontalTangentRow_indexed (k : ℂ) (u w : List (Fin 3×ℕ)) :
    horizontalTangentRow k u (indexedWord k 0 w)=
      (horizontalPairPolynomial k u (w.map lowerLetter)).coeff 1 := by
  let a := (occupationBasis k 0).repr (indexedWord k 0 w)
  have hp : horizontalPairPolynomial k u (w.map lowerLetter)=
      ∑j∈a.support,Polynomial.C (a j)*horizontalPairPolynomial k u (occupationWord j) := by
    apply Polynomial.funext
    intro h
    simp only [eval_finsetSum,eval_mul,eval_C,horizontalPairPolynomial_eval]
    have hc : (occupationBasis k h).repr (indexedWord k h w)=a :=
      indexedWord_coordinates_independent k h k 0 w
    have he := (occupationBasis k h).linearCombination_repr (indexedWord k h w)
    rw [hc] at he
    change contravariant k h _ (indexedWord k h w)=_
    rw [← he]
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
      occupationBasis_apply,smul_eq_mul]
  rw [hp,finsetSum_coeff]
  have he := congrArg (horizontalTangentRow k u)
    ((occupationBasis k 0).linearCombination_repr (indexedWord k 0 w))
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    horizontalTangentRow_basis,smul_eq_mul] at he
  simpa only [coeff_C_mul] using he.symm

/-- The tangent rule also holds for literal creation letters, including
F_0, without choosing or changing their order. -/
theorem horizontalTangentRow_lower (k : ℂ) (u : List (Fin 3×ℕ))
    (w : List (Fin 3×ℤ)) (hw : ∀an∈w,IsLower an.1 an.2) :
    horizontalTangentRow k u (currentWord (mode k 0) w (highestVector k 0))=
      (horizontalPairPolynomial k u w).coeff 1 := by
  rw [← lower_word_indexed k 0 w hw,horizontalTangentRow_indexed]
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
def horizontalNormalPair (k : ℂ) (u : List (Fin 3×ℕ)) : NormalForm→ₗ[ℂ]ℂ[X] :=
  Finsupp.linearCombination ℂ (fun t =>
    Polynomial.C (k^t.1)*X^t.2.1*horizontalPairPolynomial k u t.2.2)

/-- Evaluation of the normal-expression pairing is its actual bilinear
pairing in the corresponding Verma module. -/
theorem horizontalNormalPair_eval (k h : ℂ) (u : List (Fin 3×ℕ)) (f : NormalForm) :
    (horizontalNormalPair k u f).eval h=
      contravariant k h (indexedWord k h (u++[(1,0)]))
        (HighestNormalOrdering.evaluate (mode k h) k h (highestVector k h) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,eval_add,ihf,ihg]
  | single t z =>
    rw [horizontalNormalPair,Finsupp.linearCombination_single,evaluate_single]
    simp only [eval_smul,eval_mul,eval_C,eval_pow,eval_X,
      horizontalPairPolynomial_eval,map_smul,smul_eq_mul]

/-- Radical cancellation removes every derivative of a right normal
coefficient. Only the actual value of that expression at weight zero survives. -/
theorem horizontalTangentRow_normal (k : ℂ) (u : List (Fin 3×ℕ))
    (f : NormalForm) (hf : f∈lowerForms) :
    (horizontalNormalPair k u f).coeff 1=
      horizontalTangentRow k u
        (HighestNormalOrdering.evaluate (mode k 0) k 0 (highestVector k 0) f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    rw [horizontalNormalPair,Finsupp.linearCombination_single,one_smul,
      evaluate_single,one_smul,map_smul,horizontalTangentRow_lower k u _ ht]
    rw [Polynomial.mul_coeff_one,horizontalPairPolynomial_zero,mul_zero,add_zero]
    simp [smul_eq_mul,coeff_zero_eq_eval_zero]
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,coeff_add,ihf,ihg]
  | smul z f hf ih => simp only [map_smul,coeff_smul,ih]

/-- The first coefficient of a horizontal pairing depends only on the
actual right-hand state at weight zero, even for words with positive modes. -/
theorem horizontalTangentRow_word (k : ℂ) (u : List (Fin 3×ℕ)) (w : List (Fin 3×ℤ)) :
    horizontalTangentRow k u (currentWord (mode k 0) w (highestVector k 0))=
      (horizontalPairPolynomial k u w).coeff 1 := by
  have hp : horizontalPairPolynomial k u w=horizontalNormalPair k u (wordNormal w) := by
    apply Polynomial.funext
    intro h
    rw [horizontalPairPolynomial_eval,horizontalNormalPair_eval,
      evaluate_wordNormal (mode k h) k h (highestVector k h) (mode_comm k h) (mode_highest k h)]
  rw [hp,horizontalTangentRow_normal k u _ (wordNormal_mem_lowerForms w),
    evaluate_wordNormal (mode k 0) k 0 (highestVector k 0) (mode_comm k 0) (mode_highest k 0)]

end
end VOA.AffineVOA.HighestModule
