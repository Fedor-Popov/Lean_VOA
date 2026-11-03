/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacParabolicCoefficient
import Mathlib.Algebra.Polynomial.Roots

/-! # All-degree orders of the actual vacuum determinant

Orders are taken in the central-level variable. The horizontal cancellation
is a polynomial identity, so it remains valid when the reflected determinant
also vanishes at the chosen level.
-/
namespace VOA.Wak.Charged
open Polynomial AffineVOA.HighestModule
noncomputable section
open scoped Classical
local instance vacuumOrderFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) :=
  jointIndexFintype n c

/-- Root multiplicities of nonzero finite products add, including repeated factors. -/
theorem rootMultiplicity_finprod {ι : Type*} (s : Finset ι) (f : ι → ℂ[X])
    (hf : ∀ i ∈ s, f i ≠ 0) (k : ℂ) :
    (∏ i ∈ s, f i).rootMultiplicity k = ∑ i ∈ s, (f i).rootMultiplicity k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,
      rootMultiplicity_mul (mul_ne_zero (hf a (by simp))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (by simp [hi])))),
      ih (fun i hi => hf i (by simp [hi]))]

/-- A power repeats the root order with exactly its exponent. -/
theorem rootMultiplicity_power (f : ℂ[X]) (hf : f ≠ 0) (k : ℂ) (n : ℕ) :
    (f^n).rootMultiplicity k = n * f.rootMultiplicity k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf),ih]
    ring

/-- One real-root factor, retaining an arbitrary fixed highest weight. -/
def affineWeightRootPolynomial (h : ℂ) (i : (Fin 3×ℕ)×ℕ) : ℂ[X] :=
  Polynomial.C h - (Polynomial.C (realRootSlope i.1 : ℂ)*(X+Polynomial.C 2)+
    Polynomial.C (realRootOffset i.1 i.2 : ℂ))

theorem affineWeightRootPolynomial_eval (h k : ℂ) (i : (Fin 3×ℕ)×ℕ) :
    (affineWeightRootPolynomial h i).eval k = h-realRootWeight (k+2) i := by
  simp [affineWeightRootPolynomial,realRootWeight]

/-- The only zero-slope real root is the horizontal lowering family. -/
theorem realRootSlope_zero_horizontal (i : (Fin 3×ℕ)×ℕ) (hi : i.1.1 ≠ 2)
    (hs : realRootSlope i.1 = 0) : i.1 = (1,0) := by
  rcases i with ⟨⟨a,m⟩,r⟩
  fin_cases a <;> simp [realRootSlope,Fin.ext_iff] at * <;> omega

/-- Every nonhorizontal factor, and every nonzero horizontal constant,
is a nonzero polynomial even at levels where its value vanishes. -/
theorem affineWeightRootPolynomial_ne_zero (h : ℂ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i.1.1 ≠ 2) (hh : i.1 = (1,0) → h ≠ (i.2 : ℂ)) :
    affineWeightRootPolynomial h i ≠ 0 := by
  intro hz
  have hs := congrArg (fun p : ℂ[X] => p.coeff 1) hz
  simp only [affineWeightRootPolynomial,coeff_sub,coeff_add,coeff_C_mul,coeff_C,
    coeff_X,ite_false,ite_true,one_ne_zero,zero_add,mul_one,zero_sub] at hs
  norm_num at hs
  have hs' : realRootSlope i.1 = 0 := by exact_mod_cast hs
  have hhoriz := realRootSlope_zero_horizontal i hi hs'
  have he := congrArg (fun p : ℂ[X] => p.eval 0) hz
  dsimp only at he
  rw [affineWeightRootPolynomial_eval] at he
  have hr : realRootWeight (0+2) i = (i.2 : ℂ) := by
    simp [realRootWeight,hhoriz,realRootSlope,realRootOffset]
  rw [hr,eval_zero] at he
  exact hh hhoriz (sub_eq_zero.mp he)

/-- A nonconstant real-root factor has a simple central zero; nonzero
horizontal constants have no zero. No distinct-root assumption is used. -/
theorem affineWeightRootPolynomial_order (h k : ℂ) (i : (Fin 3×ℕ)×ℕ)
    (hp : affineWeightRootPolynomial h i ≠ 0) :
    (affineWeightRootPolynomial h i).rootMultiplicity k =
      if realRootWeight (k+2) i = h then 1 else 0 := by
  by_cases hz : realRootWeight (k+2) i = h
  · rw [if_pos hz]
    have hs : (realRootSlope i.1 : ℂ) ≠ 0 := by
      intro hs
      apply hp
      apply Polynomial.funext
      intro z
      rw [affineWeightRootPolynomial_eval,eval_zero]
      simp only [realRootWeight,hs,zero_mul,zero_add] at hz ⊢
      exact sub_eq_zero.mpr hz.symm
    have he : affineWeightRootPolynomial h i =
        Polynomial.C (-(realRootSlope i.1 : ℂ)) * (X-Polynomial.C k) := by
      apply Polynomial.funext
      intro z
      simp only [affineWeightRootPolynomial_eval,eval_mul,eval_C,eval_sub,eval_X,
        realRootWeight] at hz ⊢
      linear_combination -hz
    rw [he,rootMultiplicity_mul (mul_ne_zero
      (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hs)) (X_sub_C_ne_zero k)),
      rootMultiplicity_C,rootMultiplicity_X_sub_C_self,zero_add]
  · rw [if_neg hz]
    apply rootMultiplicity_eq_zero
    change (affineWeightRootPolynomial h i).eval k ≠ 0
    rw [affineWeightRootPolynomial_eval]
    exact sub_ne_zero.mpr (Ne.symm hz)

/-- The full fixed-highest-weight root product as a central polynomial. -/
def affineFixedWeightProduct (h : ℂ) (n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i ∈ affineKacLabels n c, (affineWeightRootPolynomial h i)^affineKacMultiplicity n c i

/-- The reflected actual Verma determinant factors into its proved leading
normalization and the explicit central root product. -/
theorem affineMinusTwoPolynomial_factor (n : ℕ) (c : ℤ) :
    affineMinusTwoPolynomial n c = affineLeadingPolynomial n c * affineFixedWeightProduct (-2) n c := by
  apply Polynomial.funext
  intro k
  rw [affineMinusTwoPolynomial_eval,eval_mul]
  have he := weightDeterminant_eq_affineKacProduct_all (k+2) n c
  simp only [add_sub_cancel_right] at he
  rw [he,eval_mul,eval_C]
  simp [affineLeadingPolynomial,eval_prod,derivativePolynomial_eval,
    affineKacProduct,affineFixedWeightProduct,affineWeightRootPolynomial_eval]

/-- Every factor of the reflected product is a nonzero polynomial. -/
theorem affineMinusTwoRoot_ne_zero (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i ∈ affineKacLabels n c) : affineWeightRootPolynomial (-2) i ≠ 0 := by
  apply affineWeightRootPolynomial_ne_zero _ _ (affineKacLabels_bounds n c i hi).1
  intro hh he
  have hreal := congrArg Complex.re he
  norm_num at hreal
  have hh : (0 : ℝ) ≤ (i.2 : ℝ) := Nat.cast_nonneg _
  linarith

/-- Every horizontal-factor-removed vacuum factor is a nonzero polynomial. -/
theorem affineVacuumRoot_ne_zero (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i ∈ (affineKacLabels n c).erase ((1,0),0)) :
    affineWeightRootPolynomial 0 i ≠ 0 := by
  apply affineWeightRootPolynomial_ne_zero _ _ (affineKacLabels_bounds n c i
    (Finset.mem_erase.mp hi).2).1
  intro hh he
  have hr : i.2 = 0 := by exact_mod_cast he.symm
  exact (Finset.mem_erase.mp hi).1 (Prod.ext hh hr)

/-- Both central root products are genuine nonzero polynomials. -/
theorem affineFixedWeightProduct_minusTwo_ne_zero (n : ℕ) (c : ℤ) :
    affineFixedWeightProduct (-2) n c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (affineMinusTwoRoot_ne_zero n c i hi)

theorem affineVacuumProduct_ne_zero (n : ℕ) (c : ℤ) : affineVacuumProduct n c ≠ 0 := by
  have he : (∏ i ∈ (affineKacLabels n c).erase ((1,0),0),
      (affineWeightRootPolynomial 0 i)^affineKacMultiplicity n c i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (affineVacuumRoot_ne_zero n c i hi)
  simpa [affineVacuumProduct,affineWeightRootPolynomial] using he

/-- Actual descendant-weighted count of nonhorizontal vacuum resonances. -/
def vacuumOrder (k : ℂ) (n : ℕ) (c : ℤ) : ℕ :=
  ∑ i ∈ (affineKacLabels n c).erase ((1,0),0),
    if realRootWeight (k+2) i = 0 then affineKacMultiplicity n c i else 0

/-- Actual descendant-weighted count of reflected highest-weight resonances. -/
def reflectedOrder (k : ℂ) (n : ℕ) (c : ℤ) : ℕ :=
  ∑ i ∈ affineKacLabels n c,
    if realRootWeight (k+2) i = -2 then affineKacMultiplicity n c i else 0

/-- The leading normalization is a nonzero polynomial. -/
theorem affineLeadingPolynomial_ne_zero (n : ℕ) (c : ℤ) :
    affineLeadingPolynomial n c ≠ 0 := by
  intro hz
  have he := affineLeadingPolynomial_eval_ne_zero 0 (by norm_num) n c
  rw [hz,eval_zero] at he
  exact he rfl

/-- The reflected denominator is a nonzero polynomial in every finite block. -/
theorem affineMinusTwoPolynomial_ne_zero (n : ℕ) (c : ℤ) :
    affineMinusTwoPolynomial n c ≠ 0 := by
  rw [affineMinusTwoPolynomial_factor]
  exact mul_ne_zero (affineLeadingPolynomial_ne_zero n c)
    (affineFixedWeightProduct_minusTwo_ne_zero n c)

/-- Polynomial horizontal cancellation in every joint block, including
an empty reflected block and the vacuum degree-zero block. -/
theorem affine_vacuum_polynomial_identity_all (n : ℕ) (c : ℤ) :
    (vacuumChevalleyPolynomial n c).det * affineMinusTwoPolynomial n (c+1) =
      Polynomial.C (vacuumDeterminantScale n c) * affineLeadingPolynomial n c *
        affineVacuumProduct n c := by
  apply Polynomial.funext
  intro k
  simp only [eval_mul,eval_C,affineMinusTwoPolynomial_eval]
  have he := weightDeterminant_vacuum_coefficient k n c
  have hf : (weightDeterminant k n c).coeff (Fintype.card (JointIndex n (c+1))) =
      (affineLeadingPolynomial n c).eval k * (affineVacuumProduct n c).eval k := by
    simpa [affineParabolicProduct,affineVacuumProduct] using
      weightDeterminant_parabolic_coefficient_all k 0 n c
  rw [hf] at he
  have hm : (vacuumChevalleyPolynomial n c).det.eval k =
      ((vacuumChevalleyPolynomial n c).map (Polynomial.eval k)).det :=
    (Polynomial.evalRingHom k).map_det _
  rw [hm]
  exact he.symm.trans (by ring)

/-- The actual vacuum determinant is nonzero as a polynomial, even when
its specialization has a radical. -/
theorem vacuumChevalleyPolynomial_det_ne_zero (n : ℕ) (c : ℤ) : (vacuumChevalleyPolynomial n c).det ≠ 0 := by
  have he := affine_vacuum_polynomial_identity_all n c
  have hn := mul_ne_zero (mul_ne_zero
    (Polynomial.C_ne_zero.mpr (vacuumDeterminantScale_ne_zero n c))
    (affineLeadingPolynomial_ne_zero n c)) (affineVacuumProduct_ne_zero n c)
  intro hz
  rw [hz,zero_mul] at he
  exact hn he.symm

/-- All collisions are counted additively by their actual multiplicities. -/
theorem affineVacuumProduct_order (k : ℂ) (n : ℕ) (c : ℤ) :
    (affineVacuumProduct n c).rootMultiplicity k = vacuumOrder k n c := by
  have he : affineVacuumProduct n c =
      ∏ i ∈ (affineKacLabels n c).erase ((1,0),0),
        (affineWeightRootPolynomial 0 i)^affineKacMultiplicity n c i := by
    simp [affineVacuumProduct,affineWeightRootPolynomial]
  rw [he,rootMultiplicity_finprod _ _ (fun i hi =>
    pow_ne_zero _ (affineVacuumRoot_ne_zero n c i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rootMultiplicity_power _ (affineVacuumRoot_ne_zero n c i hi),
    affineWeightRootPolynomial_order _ _ _ (affineVacuumRoot_ne_zero n c i hi)]
  split_ifs <;> simp

/-- Reflected determinant order at any noncritical level is exactly the
finite weighted resonant-label count. -/
theorem affineMinusTwoPolynomial_order (k : ℂ) (hk : k+2 ≠ 0) (n : ℕ) (c : ℤ) :
    (affineMinusTwoPolynomial n c).rootMultiplicity k = reflectedOrder k n c := by
  rw [affineMinusTwoPolynomial_factor,rootMultiplicity_mul
    (mul_ne_zero (affineLeadingPolynomial_ne_zero n c)
      (affineFixedWeightProduct_minusTwo_ne_zero n c))]
  rw [rootMultiplicity_eq_zero (affineLeadingPolynomial_eval_ne_zero k hk n c),zero_add]
  rw [affineFixedWeightProduct,rootMultiplicity_finprod _ _ (fun i hi =>
    pow_ne_zero _ (affineMinusTwoRoot_ne_zero n c i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rootMultiplicity_power _ (affineMinusTwoRoot_ne_zero n c i hi),
    affineWeightRootPolynomial_order _ _ _ (affineMinusTwoRoot_ne_zero n c i hi)]
  split_ifs <;> simp

/-- All-degree cancellation of actual determinant orders. No nonvanishing
of the reflected specialization is assumed; only the level is noncritical. -/
theorem vacuum_determinant_order_add_reflected (k : ℂ) (hk : k+2 ≠ 0)
    (n : ℕ) (c : ℤ) :
    (vacuumChevalleyPolynomial n c).det.rootMultiplicity k + reflectedOrder k n (c+1) =
      vacuumOrder k n c := by
  have he := congrArg (fun p : ℂ[X] => p.rootMultiplicity k)
    (affine_vacuum_polynomial_identity_all n c)
  dsimp only at he
  rw [rootMultiplicity_mul (mul_ne_zero
    (vacuumChevalleyPolynomial_det_ne_zero n c)
    (affineMinusTwoPolynomial_ne_zero n (c+1))),
    rootMultiplicity_mul (mul_ne_zero (mul_ne_zero
      (Polynomial.C_ne_zero.mpr (vacuumDeterminantScale_ne_zero n c))
      (affineLeadingPolynomial_ne_zero n c)) (affineVacuumProduct_ne_zero n c)),
    rootMultiplicity_mul (mul_ne_zero
      (Polynomial.C_ne_zero.mpr (vacuumDeterminantScale_ne_zero n c))
      (affineLeadingPolynomial_ne_zero n c)),rootMultiplicity_C,
    rootMultiplicity_eq_zero (affineLeadingPolynomial_eval_ne_zero k hk n c),
    zero_add,zero_add,affineMinusTwoPolynomial_order k hk,
    affineVacuumProduct_order] at he
  exact he

/-- Natural-subtraction form of the same exact order cancellation. -/
theorem vacuum_determinant_order (k : ℂ) (hk : k+2 ≠ 0)
    (n : ℕ) (c : ℤ) :
    (vacuumChevalleyPolynomial n c).det.rootMultiplicity k =
      vacuumOrder k n c - reflectedOrder k n (c+1) := by
  have he := vacuum_determinant_order_add_reflected k hk n c
  omega

end
end VOA.Wak.Charged
