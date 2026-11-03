/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumAdaptedFamily
import VOA.Examples.AffineSl2VermaRootFactors
import VOA.Examples.VirasoroDeterminantFirstBlock

/-!
# The first determinant coefficient in the adapted affine basis

At highest weight zero the second block is the horizontal radical. Its
first-order form is the actual form on M(k,-2). Removing exactly one weight
factor from every horizontal row leaves the vacuum block times that shifted
Verma determinant. Both blocks here are actual word Gram matrices.
-/
namespace VOA.AffineVOA.HighestModule
open Polynomial Matrix HighestNormalOrdering
open Wak.Charged (occupationWord lowerLetter adjointWord)
noncomputable section
local instance firstBlockFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c
local instance firstBlockVermaDecidable (n : ℕ) (c : ℤ) : DecidableEq (Wak.Charged.JointIndex n c) := Classical.decEq _
local instance firstBlockVacDecidable (n : ℕ) (c : ℤ) : DecidableEq (AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) := Classical.decEq _

/-- The actual highest-weight polynomial pairing of any two indexed creation words. -/
def indexedPairPolynomial (k : ℂ) (u v : List (Fin 3×ℕ)) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X]
    (wordPolynomial (adjointWord (u.map lowerLetter)++v.map lowerLetter))

/-- Its value at a highest weight is exactly the actual canonical pairing. -/
theorem indexedPairPolynomial_eval (k h : ℂ) (u v : List (Fin 3×ℕ)) :
    (indexedPairPolynomial k u v).eval h=contravariant k h (indexedWord k h u) (indexedWord k h v) := by
  rw [indexedWord,indexedWord,contravariant_wordPolynomial]
  change Polynomial.evalRingHom h (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,X] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom h).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom h (![Polynomial.C k,X] a))=![k,h] := by
    funext a
    fin_cases a <;> simp
  rw [hx]
  rfl

/-- The actual polynomial Gram matrix in the fixed adapted word family. -/
def vacuumAdaptedGram (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (VacuumAdaptedIndex n c) (VacuumAdaptedIndex n c) ℂ[X] :=
  fun i j => indexedPairPolynomial k (vacuumAdaptedWord i) (vacuumAdaptedWord j)

/-- The vacuum block with the Chevalley adjoint convention, as a polynomial
in the central level. Its normalization is inherited from the actual Verma form. -/
def vacuumChevalleyPolynomial (n : ℕ) (c : ℤ) :
    Matrix (AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c))
      (AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) ℂ[X] := fun i j =>
  MvPolynomial.eval₂Hom Polynomial.C ![X,Polynomial.C 0]
    (wordPolynomial (adjointWord ((vacuumLiftWord i.val).map lowerLetter)++
      (vacuumLiftWord j.val).map lowerLetter))

/-- The central polynomial vacuum entry evaluates to the actual lifted
weight-zero pairing, fixing its Chevalley normalization. -/
theorem vacuumChevalleyPolynomial_eval (k : ℂ) (n : ℕ) (c : ℤ)
    (i j : AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) :
    (vacuumChevalleyPolynomial n c i j).eval k=
      contravariant k 0 (indexedWord k 0 (vacuumLiftWord i.val))
        (indexedWord k 0 (vacuumLiftWord j.val)) := by
  rw [indexedWord,indexedWord,contravariant_wordPolynomial]
  change Polynomial.evalRingHom k (MvPolynomial.eval₂Hom Polynomial.C ![X,Polynomial.C 0] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom k).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom k (![X,Polynomial.C 0] a))=![k,0] := by
    funext a
    fin_cases a <;> simp
  rw [hx]
  rfl

/-- Every horizontal row has zero constant coefficient in the adapted Gram matrix. -/
theorem vacuumAdaptedGram_row_zero (k : ℂ) (n : ℕ) (c : ℤ)
    (i : Wak.Charged.JointIndex n (c+1)) (j : VacuumAdaptedIndex n c) :
    (vacuumAdaptedGram k n c (Sum.inr i) j).coeff 0=0 := by
  exact horizontalPairPolynomial_zero k i.val.toMultiset.toList _

/-- The vacuum-horizontal cross block also vanishes at weight zero by symmetry. -/
theorem vacuumAdaptedGram_cross_zero (k : ℂ) (n : ℕ) (c : ℤ)
    (i : AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c))
    (j : Wak.Charged.JointIndex n (c+1)) :
    (vacuumAdaptedGram k n c (Sum.inl i) (Sum.inr j)).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero]
  change (indexedPairPolynomial k _ _).eval 0=0
  rw [indexedPairPolynomial_eval,contravariant_symm]
  change contravariant k 0 (indexedWord k 0 (j.val.toMultiset.toList++[(1,0)])) _=0
  rw [← horizontalEmbedding_indexedWord,horizontalEmbedding_radical]
  rfl

/-- The entire first horizontal block is exactly the actual shifted Verma Gram matrix. -/
theorem vacuumAdaptedGram_first (k : ℂ) (n : ℕ) (c : ℤ)
    (i j : Wak.Charged.JointIndex n (c+1)) :
    (vacuumAdaptedGram k n c (Sum.inr i) (Sum.inr j)).coeff 1=gramMatrix k (-2) n (c+1) i j := by
  have he := horizontalPairPolynomial_first k i.val.toMultiset.toList j.val.toMultiset.toList
  simpa only [gramMatrix,occupationBasis_apply] using he

/-- The first possible adapted determinant coefficient is the actual vacuum
Chevalley determinant times the actual weight-minus-two Verma determinant. -/
theorem vacuumAdaptedGram_first_determinant (k : ℂ) (n : ℕ) (c : ℤ) :
    (vacuumAdaptedGram k n c).det.coeff (Fintype.card (Wak.Charged.JointIndex n (c+1)))=
      ((vacuumChevalleyPolynomial n c).map (Polynomial.eval k)).det*
        (weightDeterminant k n (c+1)).eval (-2) := by
  rw [PolynomialBlock.det_first_radical_coefficient _
    (vacuumAdaptedGram_row_zero k n c) (vacuumAdaptedGram_cross_zero k n c)]
  have hv : (fun i j => (vacuumAdaptedGram k n c (Sum.inl i) (Sum.inl j)).coeff 0)=
      (vacuumChevalleyPolynomial n c).map (Polynomial.eval k) := by
    funext i j
    rw [coeff_zero_eq_eval_zero]
    change (indexedPairPolynomial k _ _).eval 0=(vacuumChevalleyPolynomial n c i j).eval k
    rw [indexedPairPolynomial_eval,vacuumChevalleyPolynomial_eval]
    rfl
  have hh : (fun i j => (vacuumAdaptedGram k n c (Sum.inr i) (Sum.inr j)).coeff 1)=
      gramMatrix k (-2) n (c+1) := by
    funext i j
    exact vacuumAdaptedGram_first k n c i j
  rw [hv,hh]
  congr 1
  change _=Polynomial.evalRingHom (-2) (weightGramPolynomial k n (c+1)).det
  rw [RingHom.map_det]
  change _=((weightGramPolynomial k n (c+1)).map (Polynomial.eval (-2))).det
  rw [weightGramPolynomial_eval]

end
end VOA.AffineVOA.HighestModule
