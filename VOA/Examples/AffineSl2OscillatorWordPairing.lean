/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AnnihilationWeightLeading
import VOA.Examples.VirasoroScreeningFactorial

/-!
# Exact oscillator word coefficients

Repeated pure derivatives extract a single shifted occupation coefficient.
The multiplier is a finite product of nonzero mode weights and positive
occupation multiplicities. Thus an adjoint word pairs diagonally with its
oscillator monomials, in any chosen list order and including gamma zero.
-/
namespace VOA.Wak.Charged
open MvPolynomial
noncomputable section

/-- The occupation multiplicities of a literal oscillator list. -/
def listOccupation : List (Fin 3×ℕ)→Occupation
  | [] => 0
  | v::w => Finsupp.single v 1+listOccupation w

/-- Collecting a list into an occupation agrees with the standard multiset
construction; no sortedness is required. -/
theorem listOccupation_multiset (w : List (Fin 3×ℕ)) :
    listOccupation w=(w : Multiset (Fin 3×ℕ)).toFinsupp := by
  induction w with
  | nil => simp [listOccupation,Multiset.toFinsupp_zero]
  | cons v w ih =>
    change Finsupp.single v 1+listOccupation w=(v::ₘ(w : Multiset (Fin 3×ℕ))).toFinsupp
    rw [ih,← Multiset.singleton_add,
      Multiset.toFinsupp_add,Multiset.toFinsupp_singleton]

/-- The chosen occupation list recovers the original actual PBW index. -/
theorem listOccupation_toList (d : Occupation) : listOccupation d.toMultiset.toList=d := by
  rw [listOccupation_multiset,Multiset.coe_toList,Finsupp.toMultiset_toFinsupp]

/-- Reversing a list changes its operator order but not its occupation. -/
theorem listOccupation_reverse (w : List (Fin 3×ℕ)) : listOccupation w.reverse=listOccupation w := by
  rw [listOccupation_multiset,listOccupation_multiset,Multiset.coe_reverse]

/-- The commutative oscillator word is its occupation monomial with coefficient one. -/
theorem oscillatorMonomial_eq (w : List (Fin 3×ℕ)) :
    oscillatorMonomial w=monomial (listOccupation w) (1 : ℂ) := by
  induction w with
  | nil => simp [oscillatorMonomial,listOccupation]
  | cons v w ih => simp only [oscillatorMonomial,ih,X,monomial_mul,one_mul,listOccupation]

/-- Signed boson weight of a literal occupation is exactly its boson count
multiplied by the chosen sign, including negative signs. -/
theorem listOccupation_bosonWeight (s : ℤ) (w : List (Fin 3×ℕ)) :
    Finsupp.weight (bosonWeight s) (listOccupation w)=s*(bosonCount w : ℤ) := by
  induction w with
  | nil => simp [listOccupation,bosonCount]
  | cons v w ih =>
    simp only [listOccupation,map_add,Finsupp.weight_single,one_nsmul,ih,bosonCount]
    by_cases hv : v.1=2 <;> simp [bosonWeight,hv,mul_add]

/-- Reversal preserves the number of boson letters. -/
theorem bosonCount_reverse (w : List (Fin 3×ℕ)) : bosonCount w.reverse=bosonCount w := by
  have hh := congrArg (Finsupp.weight (bosonWeight 1)) (listOccupation_reverse w)
  simpa only [listOccupation_bosonWeight,one_mul,Int.natCast_inj] using hh

/-- Finite exact multiplier for differentiating a word while extracting
occupation e. Each step records the new positive multiplicity before recursion. -/
def derivativeMultiplier (k : ℂ) : List (Fin 3×ℕ)→Occupation→ℂ
  | [],_ => 1
  | v::w,e => annihilationWeight k v*((e v+1 : ℕ) : ℂ)*
      derivativeMultiplier k w (e+Finsupp.single v 1)

/-- Exact coefficient of an actual pure adjoint word on every Fock polynomial. -/
theorem pureAnnihilationWord_coeff (k : ℂ) (w : List (Fin 3×ℕ))
    (e : Occupation) (P : WakFock) :
    coeff e (pureAnnihilationWord k w P)=
      derivativeMultiplier k w e*coeff (e+listOccupation w) P := by
  induction w generalizing e with
  | nil => simp [pureAnnihilationWord,derivativeMultiplier,listOccupation]
  | cons v w ih =>
    simp only [pureAnnihilationWord,Module.End.mul_apply,pureAnnihilation,
      LinearMap.smul_apply,dV_apply,coeff_smul,smul_eq_mul,
      VirasoroScreening.screening_pderiv_coeff,ih,derivativeMultiplier,listOccupation]
    rw [add_assoc]
    ring

/-- Every finite derivative multiplier is nonzero at noncritical level:
all occupation multiplicities are positive and every oscillator weight is nonzero. -/
theorem derivativeMultiplier_ne_zero (k : ℂ) (hk : k+2≠0)
    (w : List (Fin 3×ℕ)) (e : Occupation) : derivativeMultiplier k w e≠0 := by
  induction w generalizing e with
  | nil => exact one_ne_zero
  | cons v w ih =>
    exact mul_ne_zero (mul_ne_zero (annihilationWeight_ne_zero k hk v)
      (by exact_mod_cast (show e v+1≠0 by omega))) (ih _)

/-- Constant extraction against a monomial is zero unless its occupation
matches the whole adjoint word, and is the explicit nonzero multiplier if it does. -/
theorem pureAnnihilationWord_pair (k : ℂ) (w : List (Fin 3×ℕ)) (e : Occupation) :
    constantCoeff (pureAnnihilationWord k w (monomial e 1))=
      if e=listOccupation w then derivativeMultiplier k w 0 else 0 := by
  change coeff 0 _=_
  rw [pureAnnihilationWord_coeff,zero_add,coeff_monomial]
  split_ifs <;> simp_all

end
end VOA.Wak.Charged
