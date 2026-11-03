/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ChargedPolynomialWords
import VOA.Examples.AffineSl2VermaRootFactors

/-!
# Highest-weight degree bounds for the actual affine Gram matrix

Actual polynomial Fock words bound every Gram entry by the number of lowering
letters in its adjoint-row/column concatenation. Summing along permutations
bounds the determinant by the total number of root creation letters. No root
multiplicity is assumed in deriving this upper bound.
-/
namespace VOA.Wak.Charged
open MvPolynomial AffineVOA.NormalOrdering
noncomputable section

/-- Extract the actual highest coefficient coefficientwise from a finite
Fock polynomial, obtaining an ordinary polynomial in the highest weight. -/
def highestFockPolynomial (P : FockPolynomial) : Polynomial ℂ :=
  PolynomialModule.equivPolynomial (PolynomialModule.map ℂ (lcoeff ℂ 0) P)

/-- Each scalar coefficient is the actual constant oscillator coefficient. -/
theorem highestFockPolynomial_coeff (P : FockPolynomial) (j : ℕ) :
    (highestFockPolynomial P).coeff j=constantCoeff (P j) := rfl

/-- Scalar evaluation commutes with highest-coefficient extraction. -/
theorem highestFockPolynomial_eval (P : FockPolynomial) (h : ℂ) :
    (highestFockPolynomial P).eval h=constantCoeff (PolynomialModule.eval h P) := by
  induction P using PolynomialModule.induction_linear with
  | zero => simp [highestFockPolynomial]
  | add P Q hP hQ => simp_all [highestFockPolynomial]
  | single j v =>
    simp [highestFockPolynomial,PolynomialModule.equivPolynomial_single,
      PolynomialModule.eval_single,Polynomial.eval_monomial,smul_eq_C_mul,mul_comm]
    exact Or.inl rfl

/-- An actual Fock coefficient bound passes to the ordinary scalar polynomial. -/
theorem highestFockPolynomial_degree {P : FockPolynomial} {d : ℕ}
    (hP : FockDegreeLE d P) : (highestFockPolynomial P).natDegree≤d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [highestFockPolynomial_coeff,hP j hj,map_zero]

/-- The normalized two-variable word polynomial specialized at a fixed
noncritical level equals the actual formal highest coefficient. -/
theorem wordPolynomial_weight_eq (k : ℂ) (hk : k+2≠0) (w : List (Fin 3×ℤ)) :
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C k,Polynomial.X]
      (AffineVOA.HighestNormalOrdering.wordPolynomial w)=
        highestFockPolynomial (polynomialWord k w 1) := by
  apply Polynomial.funext
  intro h
  rw [highestFockPolynomial_eval,polynomialWord_eval,
    AffineVOA.HighestNormalOrdering.wordPolynomial_actual k h hk]
  change Polynomial.evalRingHom h (MvPolynomial.eval₂Hom Polynomial.C _ _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom h).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom h (![Polynomial.C k,Polynomial.X] a))=![k,h] := by
    funext a; fin_cases a <;> simp
  rw [hx]
  rfl

/-- The lowering-letter count adds under concatenation. -/
theorem loweringCount_append (u v : List (Fin 3×ℤ)) :
    loweringCount (u++v)=loweringCount u+loweringCount v := by
  induction u with
  | nil => simp [loweringCount]
  | cons a u ih => simp [loweringCount,ih,Nat.add_assoc]

/-- Adjoint occupation words also exclude Cartan zero. -/
theorem adjointOccupation_no_cartan_zero (d : Occupation) :
    ∀ an∈adjointWord (occupationWord d),an.1=2→an.2≠0 := by
  intro an han ha
  obtain ⟨bn,hbn,rfl⟩ := List.mem_map.mp han
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hbn)
  rcases adjoint_lowerLetter_positive v with hp | hp
  · omega
  · rw [hp] at ha
    norm_num [Fin.ext_iff] at ha

end
end VOA.Wak.Charged
namespace VOA.AffineVOA.HighestModule
open Wak.Charged Polynomial
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Count root letters contributed by the adjoint row. -/
def rowWeightBound (d : Occupation) : ℕ := loweringCount (adjointWord (occupationWord d))

/-- Count root letters contributed by the creation column. -/
def columnWeightBound (d : Occupation) : ℕ := loweringCount (occupationWord d)

/-- Every ACTUAL Gram entry obeys its row-plus-column highest-weight bound. -/
theorem weightGramPolynomial_degree (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i j : JointIndex n c) :
    (weightGramPolynomial k n c i j).natDegree≤rowWeightBound i.val+columnWeightBound j.val := by
  change (MvPolynomial.eval₂Hom Polynomial.C _ (HighestNormalOrdering.wordPolynomial _)).natDegree≤_
  rw [wordPolynomial_weight_eq k hk]
  have hb := highestFockPolynomial_degree (polynomialWord_degree k
    (adjointWord (occupationWord i.val)++occupationWord j.val) ?_ 1)
  · simpa only [loweringCount_append,rowWeightBound,columnWeightBound] using hb
  · intro an han
    rcases List.mem_append.mp han with hi | hj
    · exact adjointOccupation_no_cartan_zero i.val an hi
    · exact occupationWord_no_cartan_zero j.val an hj

/-- The actual highest-weight determinant has the total root-letter upper
bound. This is separate from its central-level degree and does not assert sharpness. -/
theorem weightDeterminant_degree (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (weightDeterminant k n c).natDegree≤
      ∑ i : JointIndex n c,(rowWeightBound i.val+columnWeightBound i.val) := by
  classical
  rw [weightDeterminant,Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ i : JointIndex n c,(weightGramPolynomial k n c (σ i) i).natDegree)≤
        ∑ i : JointIndex n c,(rowWeightBound (σ i).val+columnWeightBound i.val) :=
      Finset.sum_le_sum (fun i _ => weightGramPolynomial_degree k hk n c (σ i) i)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      rw [Equiv.sum_comp σ (fun i : JointIndex n c => rowWeightBound i.val)]

end
end VOA.AffineVOA.HighestModule
