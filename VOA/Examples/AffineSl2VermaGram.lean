/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaContravariant

/-!
# Actual affine Verma Gram identification at all parameters

The constructed polynomial word matrix is identified with
the canonical normalized form on the actual Verma quotient. In particular,
the screening roots are roots of an actual Verma Gram determinant. This
identification does not assert a factor multiplicity or a Kac product.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering
open NormalOrdering (currentWord currentWord_append)
open Wak.Charged (Occupation occupationWord adjointWord adjointLetter JointIndex)
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Wak.Charged.jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Moving a complete word through the actual form reverses its order and
applies the Chevalley adjoint to each letter. -/
theorem contravariant_word (k h : ℂ) (w : List (Fin 3×ℤ)) (u v : Verma k h) :
    contravariant k h (currentWord (mode k h) w u) v=
      contravariant k h u (currentWord (mode k h) (adjointWord w) v) := by
  induction w generalizing v with
  | nil => simp [currentWord,adjointWord]
  | cons an w ih =>
      change contravariant k h (mode k h an.1 an.2 _) v=_
      rw [contravariant_adj,ih]
      simp only [adjointWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        currentWord_append,Module.End.mul_apply,currentWord,mul_one]
      rfl

/-- The highest-coordinate evaluation of an actual lower normal form is
its constructed two-variable scalar polynomial, even at critical level. -/
theorem highestPolynomial_verma (k h : ℂ) (f : NormalForm) (hf : f∈lowerForms) :
    highestCoordinate k h (HighestNormalOrdering.evaluate (mode k h) k h (highestVector k h) f)=
      MvPolynomial.eval ![k,h] (highestPolynomial f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [evaluate_single,one_smul,map_smul,highestPolynomial,Finsupp.linearCombination_single,one_smul]
      by_cases he : t.2.2=[]
      · simp [he,currentWord,highestCoordinate_highest]
      · rw [highestCoordinate_lower_word k h _ ht he,if_neg he]
        simp
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul z f hf ih => simp only [map_smul,ih,MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,smul_eq_mul]

/-- Every word's actual highest coefficient is evaluation of its exact
normal-ordering polynomial at level and highest weight. -/
theorem wordPolynomial_verma (k h : ℂ) (w : List (Fin 3×ℤ)) :
    highestCoordinate k h (currentWord (mode k h) w (highestVector k h))=
      MvPolynomial.eval ![k,h] (wordPolynomial w) := by
  rw [← evaluate_wordNormal (mode k h) k h (highestVector k h) (mode_comm k h) (mode_highest k h)]
  exact highestPolynomial_verma k h _ (wordNormal_mem_lowerForms w)

/-- Actual pairings of arbitrary creation words equal their two-variable
polynomials with the exact highest-vector normalization one. -/
theorem contravariant_wordPolynomial (k h : ℂ) (u v : List (Fin 3×ℤ)) :
    contravariant k h (currentWord (mode k h) u (highestVector k h))
      (currentWord (mode k h) v (highestVector k h))=
      MvPolynomial.eval ![k,h] (wordPolynomial (adjointWord u++v)) := by
  rw [contravariant_word,contravariant_highest_left,← Module.End.mul_apply,
    ← currentWord_append,wordPolynomial_verma]

/-- The actual finite Verma Gram matrix at fixed energy and root charge. -/
def gramMatrix (k h : ℂ) (n : ℕ) (c : ℤ) : Matrix (JointIndex n c) (JointIndex n c) ℂ :=
  fun i j => contravariant k h (occupationBasis k h i.val) (occupationBasis k h j.val)

/-- The polynomial matrix used for screening roots is EXACTLY the actual
Verma Gram matrix, with no noncritical-level assumption. -/
theorem highestGramPolynomial_verma (k h : ℂ) (n : ℕ) (c : ℤ) :
    (Wak.Charged.highestGramPolynomial n c).map (MvPolynomial.eval ![k,h])=gramMatrix k h n c := by
  ext i j
  simp only [Matrix.map_apply,Wak.Charged.highestGramPolynomial,gramMatrix,occupationBasis_apply]
  exact (contravariant_wordPolynomial k h (occupationWord i.val) (occupationWord j.val)).symm

/-- The determinant polynomial evaluates to the actual canonical Verma
Gram determinant, at all complex levels and weights. -/
theorem highestDeterminant_verma (k h : ℂ) (n : ℕ) (c : ℤ) :
    MvPolynomial.eval ![k,h] (Wak.Charged.highestDeterminant n c)=(gramMatrix k h n c).det := by
  rw [Wak.Charged.highestDeterminant,RingHom.map_det (MvPolynomial.eval ![k,h])]
  exact congrArg Matrix.det (highestGramPolynomial_verma k h n c)

/-- The actual finite Verma Gram matrix is symmetric. -/
theorem gramMatrix_symm (k h : ℂ) (n : ℕ) (c : ℤ) :
    (gramMatrix k h n c).transpose=gramMatrix k h n c := by
  ext i j
  exact contravariant_symm k h _ _

end
end VOA.AffineVOA.HighestModule
