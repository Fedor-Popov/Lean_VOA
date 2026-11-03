/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestWords
import VOA.Examples.AffineSl2UniversalPairing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Actual highest-word determinant roots from finite screenings

The positive-word matrix on Fock monomials has the actual nonzero screening
coefficient vector in its kernel. The general highest-word Gram matrix is
its product with the actual creation-coordinate matrix. This proves ordinary
determinant roots without assuming faithfulness or a Verma/Fock isomorphism.
-/
namespace VOA.Wak.Charged
open MvPolynomial Matrix
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord currentWord_append)
open scoped BigOperators
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Exact finite monomial expansion in the actual joint space. -/
theorem jointFock_expansion (n : ℕ) (c : ℤ) (P : WakFock) (hP : P∈jointFockSpace n c) :
    P=∑ d : JointIndex n c,coeff d.val P • monomial d.val (1 : ℂ) := by
  classical
  ext e
  rw [coeff_sum]
  simp only [coeff_smul,coeff_monomial,smul_eq_mul,mul_ite,mul_one,mul_zero]
  by_cases he : occupationEnergy e=n ∧ occupationCharge e=c
  · rw [Finset.sum_eq_single (⟨e,he⟩ : JointIndex n c)]
    · simp
    · intro d hd hde
      rw [if_neg (by intro heq; apply hde; exact Subtype.ext heq)]
    · simp
  · have hz : coeff e P=0 := by
      by_contra hn
      exact he (hP (mem_support_iff.mpr hn))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg (by intro heq; exact he (heq ▸ d.property))]

/-- The actual highest projection after a finite positive word is linear. -/
def highestRow (k lam : ℂ) (w : List (Fin 3×ℤ)) : WakFock→ₗ[ℂ]ℂ :=
  (lcoeff ℂ 0).comp (currentWord (J k lam) w)

/-- The row is exactly the actual constant coefficient of the word action. -/
theorem highestRow_apply (k lam : ℂ) (w : List (Fin 3×ℤ)) (P : WakFock) :
    highestRow k lam w P=constantCoeff (currentWord (J k lam) w P) := rfl

/-- Positive-word rows tested on actual Fock monomials at one joint label. -/
def fockRowMatrix (k lam : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  highestRow k lam (adjointWord (occupationWord i.val)) (monomial j.val 1)

/-- Actual creation-word coordinates in the same joint monomial space. -/
def creationMatrix (k lam : ℂ) (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) ℂ := fun i j =>
  coeff i.val (currentWord (J k lam) (occupationWord j.val) (1 : WakFock))

/-- The ordinary two-variable highest-word Gram polynomial matrix; its
indices include horizontal lowering and all three negative current colours. -/
def highestGramPolynomial (n : ℕ) (c : ℤ) :
    Matrix (JointIndex n c) (JointIndex n c) (MvPolynomial (Fin 2) ℂ) := fun i j =>
  wordPolynomial (adjointWord (occupationWord i.val)++occupationWord j.val)

/-- The corresponding ordinary polynomial determinant, with no proposed
factorization or nondegeneracy built into its definition. -/
def highestDeterminant (n : ℕ) (c : ℤ) : MvPolynomial (Fin 2) ℂ :=
  (highestGramPolynomial n c).det

/-- Evaluating the polynomial matrix is the ACTUAL product of the positive
Fock row matrix with actual creation coordinates. -/
theorem highestGramPolynomial_factor (k lam : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (highestGramPolynomial n c).map (MvPolynomial.eval ![k,lam])=
      fockRowMatrix k lam n c*creationMatrix k lam n c := by
  ext i j
  change MvPolynomial.eval ![k,lam] (wordPolynomial _)=_
  rw [← wordPolynomial_actual k lam hk,currentWord_append,Module.End.mul_apply,
    ← highestRow_apply]
  rw [jointFock_expansion n c _ (occupationWord_mem_joint k lam n c j),map_sum]
  simp only [map_smul,smul_eq_mul,Matrix.mul_apply,fockRowMatrix,creationMatrix]
  apply Finset.sum_congr rfl
  intro d hd
  exact mul_comm _ _

/-- The actual nonzero screening coefficient vector is in the kernel of
the finite positive-word matrix at its screening parameters. -/
theorem screening_fockRowMatrix_kernel (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    fockRowMatrix k ((q : ℂ)*(k+2)-(r : ℂ)-1) (r*q) (r : ℤ) *ᵥ
      (fun d : JointIndex (r*q) (r : ℤ) => coeff d.val (Screening.state r q M))=0 := by
  funext i
  have hz := congrArg constantCoeff (adjoint_occupation_kills_screening r q M hr hq k hMk i)
  rw [← highestRow_apply,jointFock_expansion (r*q) (r : ℤ) _
    (screening_mem_jointFockSpace r q M hq),map_sum] at hz
  simp only [map_smul,smul_eq_mul,map_zero] at hz
  change (∑ j : JointIndex (r*q) (r : ℤ),_)=0
  convert hz using 1
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Nonvanishing of the actual screening polynomial makes its finite joint
coefficient vector nonzero. No chosen coefficient normalization is assumed. -/
theorem screening_joint_coefficients_ne_zero (r q M : ℕ) (hr : 0<r) (hq : 0<q) :
    (fun d : JointIndex (r*q) (r : ℤ) => coeff d.val (Screening.state r q M))≠0 := by
  intro hz
  have he := jointFock_expansion (r*q) (r : ℤ) _ (screening_mem_jointFockSpace r q M hq)
  have hc (d : JointIndex (r*q) (r : ℤ)) : coeff d.val (Screening.state r q M)=0 := congrFun hz d
  simp only [hc,zero_smul,Finset.sum_const_zero] at he
  exact Screening.state_ne_zero r q M hr hq he

/-- The positive-word matrix has an ACTUAL determinant root at every
integer-screening parameter, proved by its nonzero coefficient kernel. -/
theorem screening_fockRowMatrix_det_zero (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    (fockRowMatrix k ((q : ℂ)*(k+2)-(r : ℂ)-1) (r*q) (r : ℤ)).det=0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨_,screening_joint_coefficients_ne_zero r q M hr hq,
    screening_fockRowMatrix_kernel r q M hr hq k hMk⟩

/-- The ordinary highest-word polynomial determinant vanishes on EVERY
reciprocal-positive-integer screening parameter. This is a genuine root of
the actual pairing matrix, not just a candidate singular vector or moment. -/
theorem highestDeterminant_screening_root (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) :
    MvPolynomial.eval ![k,(q : ℂ)*(k+2)-(r : ℂ)-1]
      (highestDeterminant (r*q) (r : ℤ))=0 := by
  have hk : k+2≠0 := by intro hz; simp [hz] at hMk
  rw [highestDeterminant,RingHom.map_det]
  change ((highestGramPolynomial (r*q) (r : ℤ)).map
    (MvPolynomial.eval ![k,(q : ℂ)*(k+2)-(r : ℂ)-1])).det=0
  rw [highestGramPolynomial_factor k _ hk,Matrix.det_mul,
    screening_fockRowMatrix_det_zero r q M hr hq k hMk,zero_mul]

end
end VOA.Wak.Charged
