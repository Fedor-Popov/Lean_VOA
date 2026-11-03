/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2FockTopMatrices
import VOA.Examples.AffineSl2HighestWeightDegree

/-!
# Polynomial matrices of actual charged Fock words

Both factors of the actual affine Gram matrix are ordinary highest-weight
polynomial matrices. Their top coefficients are the already computed actual
creation and adjoint leading matrices. This identifies polynomial degrees
with actual operator calculations, rather than assigning a formal determinant.
-/
namespace VOA.Wak.Charged
open MvPolynomial Matrix
open AffineVOA.NormalOrdering (currentWord)
noncomputable section
local instance fockPolyFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance fockPolyDecidable (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Extract any fixed oscillator coefficient from a finite Fock polynomial. -/
def fockCoefficientPolynomial (e : Occupation) (P : FockPolynomial) : Polynomial ℂ :=
  PolynomialModule.equivPolynomial (PolynomialModule.map ℂ (lcoeff ℂ e) P)

/-- Coefficients of the extracted scalar polynomial are actual oscillator coefficients. -/
theorem fockCoefficientPolynomial_coeff (e : Occupation) (P : FockPolynomial) (j : ℕ) :
    (fockCoefficientPolynomial e P).coeff j=coeff e (P j) := rfl

/-- Scalar evaluation commutes with every fixed oscillator coefficient. -/
theorem fockCoefficientPolynomial_eval (e : Occupation) (P : FockPolynomial) (h : ℂ) :
    (fockCoefficientPolynomial e P).eval h=coeff e (PolynomialModule.eval h P) := by
  induction P using PolynomialModule.induction_linear with
  | zero => simp [fockCoefficientPolynomial]
  | add P Q hP hQ => simp_all [fockCoefficientPolynomial]
  | single j v =>
    simp [fockCoefficientPolynomial,PolynomialModule.equivPolynomial_single,
      PolynomialModule.eval_single,Polynomial.eval_monomial,mul_comm]

/-- Coefficient extraction preserves the established highest-weight degree bound. -/
theorem fockCoefficientPolynomial_degree (e : Occupation) {P : FockPolynomial} {d : ℕ}
    (hP : FockDegreeLE d P) : (fockCoefficientPolynomial e P).natDegree≤d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [fockCoefficientPolynomial_coeff,hP j hj,coeff_zero]

/-- Polynomial creation-coordinate matrix of actual occupation words. -/
def creationPolynomialMatrix (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) (Polynomial ℂ) := fun i j =>
  fockCoefficientPolynomial i.val (polynomialWord k (occupationWord j.val) 1)

/-- Polynomial positive-row matrix tested on actual oscillator monomials. -/
def rowPolynomialMatrix (k : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) (Polynomial ℂ) := fun i j =>
  highestFockPolynomial (polynomialWord k (adjointWord (occupationWord i.val)) (monomial j.val 1))

/-- Every specialization of the polynomial creation matrix is the actual
creation-coordinate matrix, even at critical level. -/
theorem creationPolynomialMatrix_eval (k h : ℂ) (n : ℕ) (c : ℤ) :
    (creationPolynomialMatrix k n c).map (Polynomial.eval h)=creationMatrix k h n c := by
  ext i j
  exact (fockCoefficientPolynomial_eval _ _ _).trans (congrArg (coeff i.val) (polynomialWord_eval _ _ _ _))

/-- Every specialization of the polynomial row matrix is the actual positive-row matrix. -/
theorem rowPolynomialMatrix_eval (k h : ℂ) (n : ℕ) (c : ℤ) :
    (rowPolynomialMatrix k n c).map (Polynomial.eval h)=fockRowMatrix k h n c := by
  ext i j
  exact (highestFockPolynomial_eval _ _).trans (congrArg constantCoeff (polynomialWord_eval _ _ _ _))

/-- The creation column's highest-weight degree is bounded by its F count. -/
theorem creationPolynomialMatrix_degree (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c) :
    (creationPolynomialMatrix k n c i j).natDegree≤loweringCount (occupationWord j.val) :=
  fockCoefficientPolynomial_degree _ (polynomialWord_degree k _ (occupationWord_no_cartan_zero _) _)

/-- The positive row's degree is bounded by its adjoint F count, independently of its test column. -/
theorem rowPolynomialMatrix_degree (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c) :
    (rowPolynomialMatrix k n c i j).natDegree≤loweringCount (adjointWord (occupationWord i.val)) :=
  highestFockPolynomial_degree (polynomialWord_degree k _ (adjointOccupation_no_cartan_zero _) _)

/-- Literal leading annihilation words agree with the actual leading current
word on the corresponding adjoint letters, before any coefficient extraction. -/
theorem leadingAnnihilationWord_actual (k : ℂ) (w : List (Fin 3×ℕ)) :
    leadingAnnihilationWord k w=currentWord (leadingCurrent k)
      (w.map (fun v => adjointLetter (lowerLetter v))) := by
  induction w with
  | nil => rfl
  | cons v w ih => simp only [leadingAnnihilationWord,List.map_cons,currentWord,ih,leadingAnnihilation]

/-- The creation polynomial's top entries are precisely the
actual triangular matrix proved above. -/
theorem creationPolynomialMatrix_top (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c) :
    (creationPolynomialMatrix k n c i j).coeff (loweringCount (occupationWord j.val))=
      creationTopMatrix k n c i j := by
  rw [creationPolynomialMatrix,fockCoefficientPolynomial_coeff,
    polynomialWord_top k _ (occupationWord_no_cartan_zero _)]
  rw [creationTopMatrix,leadingCreationWord_actual]
  rfl

/-- The positive polynomial's row-top entries are exactly the actual
triangular adjoint matrix, including list reversal. -/
theorem rowPolynomialMatrix_top (k : ℂ) (n : ℕ) (c : ℤ) (i j : JointIndex n c) :
    (rowPolynomialMatrix k n c i j).coeff (loweringCount (adjointWord (occupationWord i.val)))=
      rowTopMatrix k n c i j := by
  rw [rowPolynomialMatrix,highestFockPolynomial_coeff,
    polynomialWord_top k _ (adjointOccupation_no_cartan_zero _)]
  rw [rowTopMatrix,leadingAnnihilationWord_actual]
  simp only [adjointWord,occupationWord,← List.map_reverse,List.map_map]
  rfl

/-- The actual canonical Verma Gram polynomial matrix factors into the two
actual Fock polynomial matrices at every noncritical level. -/
theorem weightGramPolynomial_fock_factor (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    AffineVOA.HighestModule.weightGramPolynomial k n c=
      rowPolynomialMatrix k n c*creationPolynomialMatrix k n c := by
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro h
  have he := highestGramPolynomial_factor k h hk n c
  rw [AffineVOA.HighestModule.highestGramPolynomial_verma] at he
  have heval : (AffineVOA.HighestModule.weightGramPolynomial k n c).map (Polynomial.evalRingHom h)=
      (rowPolynomialMatrix k n c*creationPolynomialMatrix k n c).map (Polynomial.evalRingHom h) := by
    rw [Matrix.map_mul]
    change (AffineVOA.HighestModule.weightGramPolynomial k n c).map (Polynomial.eval h)=
      (rowPolynomialMatrix k n c).map (Polynomial.eval h)*
        (creationPolynomialMatrix k n c).map (Polynomial.eval h)
    rw [AffineVOA.HighestModule.weightGramPolynomial_eval,
      rowPolynomialMatrix_eval,creationPolynomialMatrix_eval]
    exact he
  exact congrArg (fun A => A i j) heval

end
end VOA.Wak.Charged
