/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoShiftedVacuum
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Projection through actual shifted vacuum tensor factors

Every strictly negative original current raises nonnegative oscillator
energy, so its constant coefficient vanishes on EVERY input polynomial.
Consequently projecting a shifted vacuum tensor factor to its constant term
intertwines every general creation mode with the action on the other factor.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
open scoped TensorProduct
noncomputable section

/-- A negative actual current can never produce a constant term from a
polynomial of nonnegative oscillator energy, even one containing gamma zero. -/
theorem constantCoeff_negative_current (k lam : ℂ) (a : Fin 3) (m : ℤ) (hm : m<0)
    (P : WakFock) : constantCoeff (J k lam a m P)=0 := by
  have hmono (d : Occupation) : constantCoeff (J k lam a m (monomial d (1 : ℂ)))=0 := by
    have hc := congrArg (fun T : End ℂ WakFock => T (monomial d (1 : ℂ))) (degree_J k lam a m)
    dsimp only at hc
    rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
      Dwt,Eul_monomial_one,weight_wtFn,map_smul,LinearMap.smul_apply] at hc
    have he := congrArg constantCoeff hc
    simp only [map_sub,constantCoeff_Eul,smul_eq_C_mul,map_mul,constantCoeff_C] at he
    have hn : (occupationEnergy d : ℂ)-(m : ℂ)≠0 := by
      have hp : (0 : ℤ)<(occupationEnergy d : ℤ)-m := by omega
      exact_mod_cast (ne_of_gt hp)
    have hz : ((occupationEnergy d : ℂ)-(m : ℂ))*
        constantCoeff (J k lam a m (monomial d (1 : ℂ)))=0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left hn
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ,add_zero]
  | monomial d z =>
      have hz : monomial d z=z • (monomial d (1 : ℂ)) := by rw [smul_monomial]; simp only [smul_eq_mul,mul_one]
      rw [hz,map_smul,smul_eq_C_mul,map_mul,constantCoeff_C,hmono,mul_zero]

/-- Every general creation current in a shifted vacuum factor has zero
constant projection on ALL inputs, not merely on the vacuum. -/
theorem constantCoeff_shifted_current (d : ℕ) (hd : 2≤d) (k : ℂ)
    (a : Fin 3) (n : ℤ) (hn : IsLower a n) (P : WakFock) :
    constantCoeff (shiftedJ d k a n P)=0 := by
  rw [shiftedJ_lower d k (a,n) hn]
  exact constantCoeff_negative_current k 0 _ _ (shiftedLetter_negative d hd (a,n) hn) P

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Currents on a tensor product act by the sum of their two factor actions. -/
def tensorCurrent (A : Fin 3→ℤ→End ℂ V) (B : Fin 3→ℤ→End ℂ W)
    (a : Fin 3) (n : ℤ) : End ℂ (V ⊗[ℂ] W) :=
  (A a n).rTensor W+(B a n).lTensor V

/-- The literal tensor-current action on a pure tensor. -/
theorem tensorCurrent_tmul (A : Fin 3→ℤ→End ℂ V) (B : Fin 3→ℤ→End ℂ W)
    (a : Fin 3) (n : ℤ) (v : V) (w : W) :
    tensorCurrent A B a n (v ⊗ₜ[ℂ] w)=A a n v ⊗ₜ[ℂ] w+v ⊗ₜ[ℂ] B a n w := by
  simp [tensorCurrent]

/-- Project the right actual Fock factor to its vacuum constant coefficient. -/
def rightVacuumProjection : (V ⊗[ℂ] WakFock)→ₗ[ℂ]V :=
  (TensorProduct.rid ℂ V).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : V→ₗ[ℂ]V) (lcoeff ℂ 0))

/-- On a pure tensor the projection is the second factor's constant scalar
multiplying the first factor. -/
theorem rightVacuumProjection_tmul (v : V) (P : WakFock) :
    rightVacuumProjection (v ⊗ₜ[ℂ] P)=constantCoeff P • v := by
  simp [rightVacuumProjection]
  rfl

/-- Actual projection intertwines every creation current after adding a
shifted vacuum factor. Its entire right-factor contribution is zero. -/
theorem rightVacuumProjection_current (A : Fin 3→ℤ→End ℂ V)
    (d : ℕ) (hd : 2≤d) (k : ℂ) (a : Fin 3) (n : ℤ) (hn : IsLower a n)
    (x : V ⊗[ℂ] WakFock) :
    rightVacuumProjection (tensorCurrent A (shiftedJ d k) a n x)=
      A a n (rightVacuumProjection x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v P =>
      rw [tensorCurrent_tmul,map_add,rightVacuumProjection_tmul,rightVacuumProjection_tmul,
        constantCoeff_shifted_current d hd k a n hn P,zero_smul,add_zero,
        rightVacuumProjection_tmul,map_smul]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The intertwining extends to every finite creation word, without any
commutation or ordering of its letters. -/
theorem rightVacuumProjection_word (A : Fin 3→ℤ→End ℂ V)
    (d : ℕ) (hd : 2≤d) (k : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) (x : V ⊗[ℂ] WakFock) :
    rightVacuumProjection (currentWord (tensorCurrent A (shiftedJ d k)) w x)=
      currentWord A w (rightVacuumProjection x) := by
  induction w with
  | nil => rfl
  | cons an w ih =>
      rw [currentWord,Module.End.mul_apply,rightVacuumProjection_current A d hd k an.1 an.2
        (hw an (by simp)),ih (fun bn hb => hw bn (by simp [hb]))]
      rfl

end
end VOA.Wak.Charged
