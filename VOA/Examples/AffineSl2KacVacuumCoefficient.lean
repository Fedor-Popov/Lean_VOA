/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleKacLabels
import VOA.Examples.AffineSl2VacuumDeterminantCoefficient

/-!
# Removing the horizontal factor from the actual affine Kac determinant

The horizontal F0 root is identically zero in highest weight. Removing
exactly its descendant multiplicity leaves a polynomial in central level.
The actual vacuum coefficient identity then has only ordinary polynomial
factors, including the weight-minus-two denominator.
-/
namespace VOA.Wak.Charged
open Polynomial AffineVOA.HighestModule
noncomputable section
open scoped Classical
local instance vacuumKacFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- Central-level polynomial of one oscillator adjoint multiplier. -/
def annihilationPolynomial (v : Fin 3×ℕ) : ℂ[X] :=
  if v.1=0 then -1 else if v.1=1 then 1 else
    Polynomial.C (2*((v.2 : ℂ)+1))*(X+Polynomial.C 2)

/-- Evaluating that polynomial recovers the actual oscillator weight. -/
theorem annihilationPolynomial_eval (k : ℂ) (v : Fin 3×ℕ) :
    (annihilationPolynomial v).eval k=annihilationWeight k v := by
  unfold annihilationPolynomial annihilationWeight
  split_ifs <;> simp <;> ring

/-- Finite polynomial carrying every multiplicity in an adjoint word. -/
def derivativePolynomial : List (Fin 3×ℕ)→Occupation→ℂ[X]
  | [],_ => 1
  | v::w,e => annihilationPolynomial v*Polynomial.C ((e v+1 : ℕ) : ℂ)*
      derivativePolynomial w (e+Finsupp.single v 1)

/-- Its evaluation is the already proved actual derivative multiplier. -/
theorem derivativePolynomial_eval (k : ℂ) (w : List (Fin 3×ℕ)) (e : Occupation) :
    (derivativePolynomial w e).eval k=derivativeMultiplier k w e := by
  induction w generalizing e with
  | nil => simp [derivativePolynomial,derivativeMultiplier]
  | cons v w ih => simp only [derivativePolynomial,eval_mul,eval_C,
      annihilationPolynomial_eval,ih,derivativeMultiplier]

/-- Explicit central polynomial prefactor in the full normalized Kac formula. -/
def affineLeadingPolynomial (n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i : JointIndex n c,derivativePolynomial i.val.toMultiset.toList.reverse 0

/-- Its value is nonzero at every noncritical level. -/
theorem affineLeadingPolynomial_eval_ne_zero (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (affineLeadingPolynomial n c).eval k≠0 := by
  simp only [affineLeadingPolynomial,eval_prod,derivativePolynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => derivativeMultiplier_ne_zero k hk _ _)

/-- The horizontal root label belongs whenever the joint principal bound
is positive; this is the condition needed for removing its factor. -/
theorem affineKacLabels_horizontal_mem (n : ℕ) (c : ℤ) (hc : 0<2*(n : ℤ)-c) :
    ((1,0),0)∈affineKacLabels n c := by
  simp [affineKacLabels,realRootModes,jointModeBox,oscillatorEnergy,
    show 0<(2*(n : ℤ)-c).toNat by omega]

/-- The reduced highest-weight product omits only the horizontal root. -/
def affineKacWithoutHorizontal (t : ℂ) (n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i∈(affineKacLabels n c).erase ((1,0),0),
    (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i

/-- Removing the horizontal label extracts exactly the dimension of the
shifted Verma block, with no other root or multiplicity removed. -/
theorem affineKacProduct_horizontal_factor (t : ℂ) (n : ℕ) (c : ℤ)
    (hc : 0<2*(n : ℤ)-c) :
    affineKacProduct t n c=X^Fintype.card (JointIndex n (c+1))*affineKacWithoutHorizontal t n c := by
  classical
  have he := Finset.mul_prod_erase (affineKacLabels n c)
    (fun i => (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i)
    (affineKacLabels_horizontal_mem n c hc)
  simpa [affineKacProduct,affineKacWithoutHorizontal,realRootWeight,realRootSlope,
    realRootOffset,affineKacMultiplicity,oscillatorEnergy,oscillatorCharge] using he.symm

/-- The reduced constant coefficient, expressed directly as a central-level
polynomial; shifted level is X+2 throughout. -/
def affineVacuumProduct (n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i∈(affineKacLabels n c).erase ((1,0),0),
    (-(Polynomial.C (realRootSlope i.1 : ℂ)*(X+Polynomial.C 2)+
      Polynomial.C (realRootOffset i.1 i.2 : ℂ)))^affineKacMultiplicity n c i

/-- Evaluating the reduced central product equals the first nonzero
possible highest-weight coefficient after horizontal factor removal. -/
theorem affineKacProduct_first_coefficient (k : ℂ) (n : ℕ) (c : ℤ)
    (hc : 0<2*(n : ℤ)-c) :
    (affineKacProduct (k+2) n c).coeff (Fintype.card (JointIndex n (c+1)))=
      (affineVacuumProduct n c).eval k := by
  rw [affineKacProduct_horizontal_factor _ _ _ hc]
  have he := coeff_X_pow_mul (affineKacWithoutHorizontal (k+2) n c)
    (Fintype.card (JointIndex n (c+1))) 0
  simp only [zero_add] at he
  rw [he]
  simp [coeff_zero_eq_eval_zero,affineKacWithoutHorizontal,affineVacuumProduct,
    eval_prod,realRootWeight]

/-- The actual determinant at highest weight minus two, as a central
polynomial constructed from the full two-variable Gram determinant. -/
def affineMinusTwoPolynomial (n : ℕ) (c : ℤ) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![X,Polynomial.C (-2)] (highestDeterminant n c)

/-- Its evaluation is the genuine shifted Verma determinant, with no
normalization or character premise. -/
theorem affineMinusTwoPolynomial_eval (k : ℂ) (n : ℕ) (c : ℤ) :
    (affineMinusTwoPolynomial n c).eval k=(weightDeterminant k n c).eval (-2) := by
  rw [weightDeterminant_eval_highest]
  change Polynomial.evalRingHom k (MvPolynomial.eval₂Hom Polynomial.C ![X,Polynomial.C (-2)] _)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom k).comp Polynomial.C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom k (![X,Polynomial.C (-2)] a))=![k,-2] := by
    funext a; fin_cases a <;> simp
  rw [hx]
  rfl

/-- Exact polynomial identity separating the actual vacuum determinant
from the shifted Verma determinant and the explicit reduced Kac product. -/
theorem affine_vacuum_polynomial_identity (n : ℕ) (c : ℤ)
    (hc : 0<2*(n : ℤ)-c) :
    (vacuumChevalleyPolynomial n c).det*affineMinusTwoPolynomial n (c+1)=
      Polynomial.C (vacuumDeterminantScale n c)*affineLeadingPolynomial n c*affineVacuumProduct n c := by
  apply Polynomial.funext
  intro k
  simp only [eval_mul,eval_C,affineMinusTwoPolynomial_eval,affineLeadingPolynomial,
    eval_prod,derivativePolynomial_eval]
  have he := weightDeterminant_vacuum_coefficient k n c
  have hf := weightDeterminant_eq_affineKacProduct_all (k+2) n c
  simp only [add_sub_cancel_right] at hf
  rw [hf,coeff_C_mul,affineKacProduct_first_coefficient k n c hc] at he
  have hm : (vacuumChevalleyPolynomial n c).det.eval k=
      ((vacuumChevalleyPolynomial n c).map (Polynomial.eval k)).det :=
    (Polynomial.evalRingHom k).map_det _
  rw [hm]
  exact he.symm.trans (by ring)

end
end VOA.Wak.Charged
