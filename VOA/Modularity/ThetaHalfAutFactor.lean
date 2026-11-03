/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GammaThetaStatement
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# A principal square-root automorphy factor

The principal complex square root of `j(A,τ) = cτ+d` gives a half-automorphy factor on every
subgroup of `SL₂(ℤ)`.  Its failure to be a strict cocycle is the quotient

`sqrt(j(AB,τ)) / (sqrt(j(A,Bτ)) sqrt(j(B,τ)))`.

The square of this quotient is `1`.  It is continuous in `τ`, and the upper half-plane is
connected, so it is constant.  Evaluating at `τ = i` therefore supplies the multiplier required
by `SlashSub.HalfAutFactor`.

This construction is independent of parity and of vertex algebras.  No metaplectic-group API is
needed: the elementary connectedness argument builds exactly the cocycle datum required by the
repository's structure.
-/

namespace VOA

open scoped MatrixGroups

universe u

namespace SlashSub

/-- The principal complex square root squares to a nonzero complex number. -/
theorem sqrt_sq_of_ne_zero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ (2 : ℕ) = z := by
  rw [sqrt_eq_exp hz, pow_two, ← Complex.exp_add]
  rw [show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring]
  exact Complex.exp_log hz

/-- The chosen principal square root of `cτ+d`. -/
noncomputable def principalHalfRoot (A : SL(2, ℤ)) (τ : UpperHalfPlane) : ℂ :=
  Complex.sqrt (autFactor A τ)

theorem principalHalfRoot_sq (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalHalfRoot A τ ^ (2 : ℕ) = autFactor A τ :=
  sqrt_sq_of_ne_zero (autFactor_ne_zero A τ)

theorem principalHalfRoot_ne_zero (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalHalfRoot A τ ≠ 0 := by
  intro h
  have hs := principalHalfRoot_sq A τ
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact autFactor_ne_zero A τ hs.symm

theorem continuous_autFactor (A : SL(2, ℤ)) :
    Continuous (fun τ : UpperHalfPlane => autFactor A τ) := by
  unfold autFactor
  fun_prop

/-- The modular action of a fixed integral special-linear matrix is continuous. -/
theorem continuous_SL2Z_smul (A : SL(2, ℤ)) :
    Continuous (fun τ : UpperHalfPlane => A • τ) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  rw [show (UpperHalfPlane.coe ∘ fun τ : UpperHalfPlane => A • τ) =
      fun τ : UpperHalfPlane =>
        (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ)
          + ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) / autFactor A τ by
    funext τ
    exact coe_SL_smul A τ]
  exact ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const).div
    (continuous_autFactor A) (fun τ => autFactor_ne_zero A τ)

/-- The principal root is continuous on the upper half-plane.  If `c = 0` the automorphy factor
is constant.  If `c ≠ 0`, its imaginary part is `c Im(τ) ≠ 0`, away from the square root's
branch cut. -/
theorem continuous_principalHalfRoot (A : SL(2, ℤ)) :
    Continuous (principalHalfRoot A) := by
  rw [continuous_iff_continuousAt]
  intro τ
  unfold principalHalfRoot
  by_cases hc : (A 1 0 : ℤ) = 0
  · simp only [autFactor, hc, Int.cast_zero, zero_mul, zero_add]
    exact continuousAt_const
  · change ContinuousAt (Complex.sqrt ∘ fun z : UpperHalfPlane => autFactor A z) τ
    have him : (autFactor A τ).im = ((A 1 0 : ℤ) : ℝ) * τ.im := by
      simp [autFactor, Complex.add_im, Complex.mul_im]
    have him0 : (autFactor A τ).im ≠ 0 := by
      rw [him]
      exact mul_ne_zero (Int.cast_ne_zero.mpr hc) τ.im_ne_zero
    exact (Complex.continuousAt_sqrt (Or.inr him0)).comp
      (continuous_autFactor A).continuousAt

/-- The pointwise obstruction to multiplicativity of the principal square root. -/
noncomputable def principalRootCocycle (A B : SL(2, ℤ)) (τ : UpperHalfPlane) : ℂ :=
  principalHalfRoot (A * B) τ /
    (principalHalfRoot A (B • τ) * principalHalfRoot B τ)

/-- The obstruction is a sign. -/
theorem principalRootCocycle_sq (A B : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalRootCocycle A B τ ^ (2 : ℕ) = 1 := by
  rw [principalRootCocycle, div_pow, mul_pow, principalHalfRoot_sq,
    principalHalfRoot_sq, principalHalfRoot_sq, autFactor_mul]
  exact div_self (mul_ne_zero (autFactor_ne_zero A (B • τ)) (autFactor_ne_zero B τ))

theorem principalRootCocycle_ne_zero (A B : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalRootCocycle A B τ ≠ 0 := by
  intro h
  have hs := principalRootCocycle_sq A B τ
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact zero_ne_one hs

theorem continuous_principalRootCocycle (A B : SL(2, ℤ)) :
    Continuous (principalRootCocycle A B) := by
  unfold principalRootCocycle
  exact (continuous_principalHalfRoot (A * B)).div
    ((continuous_principalHalfRoot A).comp (continuous_SL2Z_smul B) |>.mul
      (continuous_principalHalfRoot B))
    (fun τ => mul_ne_zero (principalHalfRoot_ne_zero A (B • τ))
      (principalHalfRoot_ne_zero B τ))

/-- The sign obstruction is independent of `τ`. -/
theorem principalRootCocycle_eq_at_I (A B : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalRootCocycle A B τ = principalRootCocycle A B UpperHalfPlane.I := by
  let f : UpperHalfPlane → ℂ := principalRootCocycle A B
  let g : UpperHalfPlane → ℂ := fun _ => principalRootCocycle A B UpperHalfPlane.I
  have hf : Continuous f := continuous_principalRootCocycle A B
  have hg : Continuous g := continuous_const
  have hsq : Set.EqOn (f ^ 2) (g ^ 2) Set.univ := by
    intro z _
    change principalRootCocycle A B z ^ (2 : ℕ) =
      principalRootCocycle A B UpperHalfPlane.I ^ (2 : ℕ)
    rw [principalRootCocycle_sq, principalRootCocycle_sq]
  have hgne : ∀ {z : UpperHalfPlane}, z ∈ Set.univ → g z ≠ 0 := by
    intro z _
    exact principalRootCocycle_ne_zero A B UpperHalfPlane.I
  have hall := isPreconnected_univ.eq_of_sq_eq hf.continuousOn hg.continuousOn hsq hgne
    (y := UpperHalfPlane.I) (Set.mem_univ _) rfl
  exact hall (Set.mem_univ _)

/-- The constant multiplier, obtained by evaluating the principal-root cocycle at `i`. -/
noncomputable def principalHalfMultiplier (A B : SL(2, ℤ)) : ℂ :=
  principalRootCocycle A B UpperHalfPlane.I

theorem principalHalfMultiplier_sq (A B : SL(2, ℤ)) :
    principalHalfMultiplier A B ^ (2 : ℕ) = 1 :=
  principalRootCocycle_sq A B UpperHalfPlane.I

theorem principalHalfRoot_cocycle (A B : SL(2, ℤ)) (τ : UpperHalfPlane) :
    principalHalfRoot (A * B) τ =
      principalHalfMultiplier A B * (principalHalfRoot A (B • τ) * principalHalfRoot B τ) := by
  rw [principalHalfMultiplier, ← principalRootCocycle_eq_at_I A B τ, principalRootCocycle]
  rw [div_mul_cancel₀ _
    (mul_ne_zero (principalHalfRoot_ne_zero A (B • τ)) (principalHalfRoot_ne_zero B τ))]

/-- A genuine half-automorphy factor on an arbitrary modular subgroup. -/
noncomputable def principalHalfAutFactor (Γ : Subgroup SL(2, ℤ)) : HalfAutFactor Γ where
  sq := principalHalfRoot
  sq_sq := by
    intro A _ τ
    simpa using principalHalfRoot_sq A τ
  sq_ne_zero := fun A _ τ => principalHalfRoot_ne_zero A τ
  mult := principalHalfMultiplier
  cocycle := fun A _ B _ τ => principalHalfRoot_cocycle A B τ
  sq_one := by
    intro τ
    simp [principalHalfRoot, autFactor_one]

/-- The required half-automorphy factor on the theta group. -/
noncomputable def thetaHalfAutFactor : HalfAutFactor thetaGroup :=
  principalHalfAutFactor thetaGroup

end SlashSub

namespace GammaThetaStmt

/-- A half-automorphy factor exists on all of `Γ_θ` (item T5 of `GammaThetaStatement`). -/
theorem thetaHalfAutFactorExists : ThetaHalfAutFactorExists :=
  ⟨SlashSub.thetaHalfAutFactor⟩

end GammaThetaStmt

end VOA
