/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaUniformStraightening

/-!
# Polynomial families of actual Verma Ward equations

Charge and highest weight may belong to any commutative complex algebra.
Recursive commutation gives polynomial combinations of negative words.
Charge-independent straightening identifies their actual PBW coefficients.
Specializing both formal variables gives the actual Ward matrix at every (c,h);
its generic kernel is not constructed by this module.
-/
namespace VOA.InverseDS.VirasoroVerma
open Polynomial VirModule LeeYangWardClosure
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Polynomial coefficients of finitely many unsorted negative words. -/
abbrev VermaPolynomialForm (R : Type*) [CommRing R] := List ℕ →₀ R

/-- Prefix a negative mode in each term, retaining polynomial coefficients. -/
noncomputable def polynomialPrepend (i : ℕ) :
    VermaPolynomialForm R →ₗ[R] VermaPolynomialForm R :=
  Finsupp.lmapDomain R R (List.cons i)

/-- Commute one mode through a negative word. The highest vector is killed
by positive modes, L₀ acts by H, and opposite modes contribute the charge C.
Negative modes are retained as creation operators, including L₋₁. -/
noncomputable def vermaModePolynomial (C H : R) (m : ℤ) :
    List ℕ → VermaPolynomialForm R
  | [] => if m<0 then Finsupp.single [(-m-1).toNat] 1 else
      if m=0 then Finsupp.single [] H else 0
  | i::w => if m<0 then Finsupp.single ((-m-1).toNat::i::w) 1 else
      polynomialPrepend i (vermaModePolynomial C H m w) +
      (algebraMap ℂ R) ((m:ℂ)+(i:ℂ)+1) • vermaModePolynomial C H (m-(i:ℤ)-1) w +
      if m-(i:ℤ)-1=0 then Finsupp.single w ((algebraMap ℂ R) (((m:ℂ)^3-m)/12)*C) else 0

/-- Evaluate the polynomial coefficients and interpret the negative words
in the actual Verma module at the evaluated charge and highest weight. -/
noncomputable def evaluatePolynomialForm (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (f : VermaPolynomialForm R) : Verma (ev C) (ev H) :=
  f.sum (fun w a => ev a • negWord (ev C) (ev H) w)

/-- A single term evaluates to its stated scalar multiple of a word. -/
theorem evaluatePolynomialForm_single (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (w : List ℕ) (a : R) :
    evaluatePolynomialForm C H ev (Finsupp.single w a)=
      ev a • negWord (ev C) (ev H) w := by
  classical
  simp [evaluatePolynomialForm]

/-- Evaluation preserves addition of finite polynomial word expressions. -/
theorem evaluatePolynomialForm_add (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (f g : VermaPolynomialForm R) :
    evaluatePolynomialForm C H ev (f+g)=
      evaluatePolynomialForm C H ev f+evaluatePolynomialForm C H ev g := by
  classical
  exact Finsupp.sum_add_index (by simp) (by intros; simp [add_smul])

/-- Multiplying a polynomial expression by a scalar polynomial evaluates
that scalar at the same parameter. -/
theorem evaluatePolynomialForm_smul (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (a : R) (f : VermaPolynomialForm R) :
    evaluatePolynomialForm C H ev (a • f)=ev a • evaluatePolynomialForm C H ev f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [evaluatePolynomialForm]
  | add f g hf hg => simp only [smul_add,evaluatePolynomialForm_add,hf,hg]
  | single w b =>
    rw [Finsupp.smul_single,evaluatePolynomialForm_single,evaluatePolynomialForm_single]
    simp [smul_eq_mul,mul_smul]

/-- Prefixing a word expression evaluates to the actual negative mode. -/
theorem evaluatePolynomialForm_prepend (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (i : ℕ) (f : VermaPolynomialForm R) :
    evaluatePolynomialForm C H ev (polynomialPrepend i f)=
      vermaMode (ev C) (ev H) (-(i:ℤ)-1) (evaluatePolynomialForm C H ev f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [evaluatePolynomialForm]
  | add f g hf hg => simp only [map_add,evaluatePolynomialForm_add,hf,hg]
  | single w a =>
    simp [polynomialPrepend,Finsupp.lmapDomain_apply,evaluatePolynomialForm_single]

/-- The recursive polynomial expression equals the actual mode action at
EVERY parameter, including parameters where a later rational singular formula
may have poles. No parameter-dependent basis choice enters this identity. -/
theorem evaluate_vermaModePolynomial (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (m : ℤ) (w : List ℕ) :
    evaluatePolynomialForm C H ev (vermaModePolynomial C H m w)=
      vermaMode (ev C) (ev H) m (negWord (ev C) (ev H) w) := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m<0
    · have he : -(((-m-1).toNat:ℕ):ℤ)-1=m := by omega
      simp [vermaModePolynomial,hm,evaluatePolynomialForm_single,he]
    · by_cases hz : m=0
      · subst m
        simp [vermaModePolynomial,evaluatePolynomialForm_single,vermaMode,verma_zero_acts]
      · simp [vermaModePolynomial,hm,hz,evaluatePolynomialForm,vermaMode,
          verma_pos_annihilate _ _ m (by omega)]
  | cons i w ih =>
    by_cases hm : m<0
    · have he : -(((-m-1).toNat:ℕ):ℤ)-1=m := by omega
      simp [vermaModePolynomial,hm,evaluatePolynomialForm_single,he]
    · rw [vermaModePolynomial,if_neg hm,evaluatePolynomialForm_add,
        evaluatePolynomialForm_add,evaluatePolynomialForm_smul,
        evaluatePolynomialForm_prepend,ih,ih]
      rw [negWord_cons,vermaMode_comm_apply (ev C) (ev H) m (-(i:ℤ)-1)]
      have he : m+(-(i:ℤ)-1)=m-(i:ℤ)-1 := by omega
      rw [he]
      split_ifs <;> simp only [evaluatePolynomialForm_single,map_mul,AlgHom.commutes,Algebra.algebraMap_self_apply,
        LinearMap.smul_apply,Module.End.one_apply]
      all_goals try simp only [evaluatePolynomialForm,Finsupp.sum_zero_index]
      all_goals push_cast
      all_goals module


/-- Straighten an expression using the constant coefficients computed at
(0,0), embedded into the coefficient algebra. This produces one PBW
coordinate without making a parameter-dependent choice. -/
noncomputable def polynomialFormCoordinate (f : VermaPolynomialForm R)
    (s : {w : List ℕ // SortedWord w}) : R :=
  f.sum (fun w a => a * algebraMap ℂ R ((vermaSortedBasis 0 0).repr (negWord 0 0 w) s))

/-- Coordinate extraction preserves addition of finite expressions. -/
theorem polynomialFormCoordinate_add (f g : VermaPolynomialForm R)
    (s : {w : List ℕ // SortedWord w}) :
    polynomialFormCoordinate (f+g) s=polynomialFormCoordinate f s+polynomialFormCoordinate g s := by
  classical
  exact Finsupp.sum_add_index (by simp) (by intros; simp [add_mul])

/-- The constructed coefficient specializes to the ACTUAL PBW coordinate.
This uses uniform negative-word straightening and the faithful Verma basis. -/
theorem polynomialFormCoordinate_eval (C H : R) (ev : R →ₐ[ℂ] ℂ)
    (f : VermaPolynomialForm R) (s : {w : List ℕ // SortedWord w}) :
    ev (polynomialFormCoordinate f s)=
      (vermaSortedBasis (ev C) (ev H)).repr (evaluatePolynomialForm C H ev f) s := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [polynomialFormCoordinate,evaluatePolynomialForm]
  | add f g hf hg =>
    simp only [polynomialFormCoordinate_add,map_add,evaluatePolynomialForm_add,
      Finsupp.add_apply,hf,hg]
  | single w a =>
    simp [polynomialFormCoordinate,evaluatePolynomialForm_single,
      verma_negWord_coordinates_independent (ev C) (ev H) 0 0 w]

/-- The Ward matrix over an arbitrary coefficient algebra, constructed by
recursive commutation and constant straightening rather than postulated. -/
noncomputable def vermaAlgebraWardMatrix (C H : R) (n : ℕ) :
    Matrix VermaWardRows (VermaPartitions n) R := fun row col =>
  polynomialFormCoordinate (vermaModePolynomial C H (if row.1=0 then 1 else 2) col.val) row.2

/-- Every specialization of the constructed matrix is exactly the actual
Verma Ward matrix. There is no remaining matrix-identification hypothesis. -/
theorem vermaAlgebraWardMatrix_eval (C H : R) (ev : R →ₐ[ℂ] ℂ) (n : ℕ) :
    (vermaAlgebraWardMatrix C H n).map ev.toRingHom=vermaWardMatrix (ev C) (ev H) n := by
  ext row col
  exact (polynomialFormCoordinate_eval C H ev _ _).trans
    (congrArg (fun v => (vermaSortedBasis (ev C) (ev H)).repr v row.2)
      (evaluate_vermaModePolynomial C H ev _ _))

/-- The universal Ward matrix has two independent polynomial variables:
variable zero is central charge, and variable one is highest weight. -/
noncomputable def vermaUniversalWardMatrix (n : ℕ) :
    Matrix VermaWardRows (VermaPartitions n) (MvPolynomial (Fin 2) ℂ) :=
  vermaAlgebraWardMatrix (MvPolynomial.X 0) (MvPolynomial.X 1) n

/-- Substituting any complex charge and weight into the universal polynomial
matrix recovers the actual L₁/L₂ equations in M(c,h). -/
theorem vermaUniversalWardMatrix_eval (c h : ℂ) (n : ℕ) :
    (vermaUniversalWardMatrix n).map
      (MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)).toRingHom=
      vermaWardMatrix c h n := by
  simpa [vermaUniversalWardMatrix] using vermaAlgebraWardMatrix_eval
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))
    (MvPolynomial.aeval (fun i : Fin 2 => if i=0 then c else h)) n

/-- On any polynomial path of charges and highest weights, a nonzero
generic rational Ward kernel specializes to a nonzero actual highest-weight
state. Constructing that kernel is the remaining representation-theory input. -/
theorem verma_highest_of_polynomial_ward (C H : Polynomial ℂ) (n : ℕ)
    (v : VermaPartitions n → RatFunc ℂ) (hv : v≠0)
    (hAv : ((vermaAlgebraWardMatrix C H n).map
      (algebraMap (Polynomial ℂ) (RatFunc ℂ))).mulVec v=0) (t : ℂ) :
    ∃ w : Verma (C.eval t) (H.eval t), w≠0 ∧ w∈sortedSpan (C.eval t) (H.eval t) n ∧
      IsHighestWeightVector (vermaRep (C.eval t) (H.eval t)) w (C.eval t) (H.eval t+n) := by
  apply verma_highest_of_generic_ward _ _ n (vermaAlgebraWardMatrix C H n) v hv hAv t
  simpa using vermaAlgebraWardMatrix_eval C H (Polynomial.aeval t) n

end VOA.InverseDS.VirasoroVerma
