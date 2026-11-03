/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.Dong
import VOA.Core.ReconstructionExistence
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Fields acting on one factor of a tensor product

This file supplies the operator-level tensor machinery used before both factors have been
packaged as vertex algebras.  A field on `A` lifts to `A ⊗ B` by acting on the first factor,
and a field on `B` lifts by acting on the second factor.  The lifts preserve lower truncation,
locality, derivatives, normal products, and translation covariance.  Fields on different factors
commute coefficientwise, so their normal product is their ordinary tensor-product convolution.
-/

namespace VOA
namespace TensorFieldLift

open Module (End)
open scoped TensorProduct

universe u v

variable {A : Type u} {B : Type v}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

noncomputable section

/-! ## One- and two-variable lifts -/

/-- Lift a field on `A` to `A ⊗ B`, acting on the first tensor factor. -/
noncomputable def firstField (f : FormalDist (End ℂ A)) :
    FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  fun n => LinearMap.rTensor B (f n)

/-- Lift a field on `B` to `A ⊗ B`, acting on the second tensor factor. -/
noncomputable def secondField (g : FormalDist (End ℂ B)) :
    FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  fun n => LinearMap.lTensor A (g n)

noncomputable def firstDist₂ (F : FormalDist₂ (End ℂ A)) :
    FormalDist₂ (End ℂ (A ⊗[ℂ] B)) :=
  fun m n => LinearMap.rTensor B (F m n)

noncomputable def secondDist₂ (G : FormalDist₂ (End ℂ B)) :
    FormalDist₂ (End ℂ (A ⊗[ℂ] B)) :=
  fun m n => LinearMap.lTensor A (G m n)

@[simp] theorem firstField_tmul (f : FormalDist (End ℂ A)) (n : ℤ) (a : A) (b : B) :
    firstField f n (a ⊗ₜ[ℂ] b) = f n a ⊗ₜ[ℂ] b := by
  rw [firstField, LinearMap.rTensor_tmul]

@[simp] theorem secondField_tmul (g : FormalDist (End ℂ B)) (n : ℤ) (a : A) (b : B) :
    secondField g n (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] g n b := by
  rw [secondField, LinearMap.lTensor_tmul]

@[simp] theorem firstDist₂_zero :
    firstDist₂ (B := B) (0 : FormalDist₂ (End ℂ A)) = 0 := by
  funext m n
  exact LinearMap.rTensor_zero B

@[simp] theorem secondDist₂_zero :
    secondDist₂ (A := A) (0 : FormalDist₂ (End ℂ B)) = 0 := by
  funext m n
  exact LinearMap.lTensor_zero A

theorem first_mul (f g : End ℂ A) :
    LinearMap.rTensor B (f * g)
      = LinearMap.rTensor B f * LinearMap.rTensor B g := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp]

theorem second_mul (f g : End ℂ B) :
    LinearMap.lTensor A (f * g)
      = LinearMap.lTensor A f * LinearMap.lTensor A g := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp]

/-! ## Brackets, difference operators, and locality -/

theorem bracketDist_firstField (f g : FormalDist (End ℂ A)) :
    bracketDist (firstField (B := B) f) (firstField g) =
      firstDist₂ (B := B) (bracketDist f g) := by
  funext m n
  rw [bracketDist_apply]
  change LinearMap.rTensor B (f m) * LinearMap.rTensor B (g n)
      - LinearMap.rTensor B (g n) * LinearMap.rTensor B (f m)
    = LinearMap.rTensor B ((bracketDist f g) m n)
  rw [bracketDist_apply]
  rw [← first_mul, ← first_mul, ← LinearMap.rTensor_sub]

theorem bracketDist_secondField (f g : FormalDist (End ℂ B)) :
    bracketDist (secondField (A := A) f) (secondField g) =
      secondDist₂ (A := A) (bracketDist f g) := by
  funext m n
  rw [bracketDist_apply]
  change LinearMap.lTensor A (f m) * LinearMap.lTensor A (g n)
      - LinearMap.lTensor A (g n) * LinearMap.lTensor A (f m)
    = LinearMap.lTensor A ((bracketDist f g) m n)
  rw [bracketDist_apply]
  rw [← second_mul, ← second_mul, ← LinearMap.lTensor_sub]

theorem mulBySub_firstDist₂ (F : FormalDist₂ (End ℂ A)) :
    mulBySub (firstDist₂ (B := B) F) = firstDist₂ (B := B) (mulBySub F) := by
  funext m n
  rw [mulBySub_apply]
  change LinearMap.rTensor B (F (m - 1) n) - LinearMap.rTensor B (F m (n - 1))
    = LinearMap.rTensor B ((mulBySub F) m n)
  rw [mulBySub_apply]
  rw [← LinearMap.rTensor_sub]

theorem mulBySub_secondDist₂ (F : FormalDist₂ (End ℂ B)) :
    mulBySub (secondDist₂ (A := A) F) = secondDist₂ (A := A) (mulBySub F) := by
  funext m n
  rw [mulBySub_apply]
  change LinearMap.lTensor A (F (m - 1) n) - LinearMap.lTensor A (F m (n - 1))
    = LinearMap.lTensor A ((mulBySub F) m n)
  rw [mulBySub_apply]
  rw [← LinearMap.lTensor_sub]

theorem mulBySubPow_firstDist₂ (N : ℕ) (F : FormalDist₂ (End ℂ A)) :
    mulBySubPow N (firstDist₂ (B := B) F) =
      firstDist₂ (B := B) (mulBySubPow N F) := by
  induction N generalizing F with
  | zero => rfl
  | succ n ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySub_firstDist₂,
        ← LinearMap.comp_apply, ← mulBySubPow_succ]

theorem mulBySubPow_secondDist₂ (N : ℕ) (F : FormalDist₂ (End ℂ B)) :
    mulBySubPow N (secondDist₂ (A := A) F) =
      secondDist₂ (A := A) (mulBySubPow N F) := by
  induction N generalizing F with
  | zero => rfl
  | succ n ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySub_secondDist₂,
        ← LinearMap.comp_apply, ← mulBySubPow_succ]

theorem local_firstField {f g : FormalDist (End ℂ A)} (h : Local f g) :
    Local (firstField (B := B) f) (firstField g) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [bracketDist_firstField, mulBySubPow_firstDist₂, hN,
    firstDist₂_zero]⟩

theorem local_secondField {f g : FormalDist (End ℂ B)} (h : Local f g) :
    Local (secondField (A := A) f) (secondField g) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [bracketDist_secondField, mulBySubPow_secondDist₂, hN,
    secondDist₂_zero]⟩

/-! ## Lower truncation -/

theorem isField_firstField {f : FormalDist (End ℂ A)} (hf : IsField f) :
    IsField (firstField (B := B) f) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (firstField f n).map_zero⟩
  | tmul a b =>
      obtain ⟨N, hN⟩ := hf a
      exact ⟨N, fun n hn => by rw [firstField_tmul, hN n hn, TensorProduct.zero_tmul]⟩
  | add x y hx hy =>
      obtain ⟨Nx, hx⟩ := hx
      obtain ⟨Ny, hy⟩ := hy
      exact ⟨min Nx Ny, fun n hn => by
        rw [map_add, hx n (lt_of_lt_of_le hn (min_le_left _ _)),
          hy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩

theorem isField_secondField {g : FormalDist (End ℂ B)} (hg : IsField g) :
    IsField (secondField (A := A) g) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (secondField g n).map_zero⟩
  | tmul a b =>
      obtain ⟨N, hN⟩ := hg b
      exact ⟨N, fun n hn => by rw [secondField_tmul, hN n hn, TensorProduct.tmul_zero]⟩
  | add x y hx hy =>
      obtain ⟨Nx, hx⟩ := hx
      obtain ⟨Ny, hy⟩ := hy
      exact ⟨min Nx Ny, fun n hn => by
        rw [map_add, hx n (lt_of_lt_of_le hn (min_le_left _ _)),
          hy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩

/-! ## Different factors commute exactly -/

theorem firstField_mul_secondField (f : FormalDist (End ℂ A))
    (g : FormalDist (End ℂ B)) (m n : ℤ) :
    firstField (B := B) f m * secondField (A := A) g n =
      secondField g n * firstField f m := by
  simp only [firstField, secondField, Module.End.mul_eq_comp,
    LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

theorem firstField_commute_secondField (f : FormalDist (End ℂ A))
    (g : FormalDist (End ℂ B)) (m n : ℤ) :
    Commute (firstField (B := B) f m) (secondField (A := A) g n) :=
  firstField_mul_secondField f g m n

theorem bracketDist_firstField_secondField (f : FormalDist (End ℂ A))
    (g : FormalDist (End ℂ B)) :
    bracketDist (firstField (B := B) f) (secondField (A := A) g) = 0 := by
  refine FormalDist₂.ext fun m n => ?_
  change firstField f m * secondField g n - secondField g n * firstField f m =
    (0 : End ℂ (A ⊗[ℂ] B))
  rw [firstField_mul_secondField, sub_self]

theorem local_firstField_secondField (f : FormalDist (End ℂ A))
    (g : FormalDist (End ℂ B)) :
    Local (firstField (B := B) f) (secondField (A := A) g) :=
  local_of_bracketDist_eq_zero (bracketDist_firstField_secondField f g)

/-! ## Derivatives and translation covariance -/

theorem deriv_firstField (f : FormalDist (End ℂ A)) :
    deriv (firstField (B := B) f) = firstField (deriv f) := by
  funext n
  change (n + 1) • LinearMap.rTensor B (f (n + 1))
    = LinearMap.rTensor B ((deriv f) n)
  rw [deriv_apply]
  exact (map_zsmul (LinearMap.rTensorHom B) (n + 1) (f (n + 1))).symm

theorem deriv_secondField (g : FormalDist (End ℂ B)) :
    deriv (secondField (A := A) g) = secondField (deriv g) := by
  funext n
  change (n + 1) • LinearMap.lTensor A (g (n + 1))
    = LinearMap.lTensor A ((deriv g) n)
  rw [deriv_apply]
  exact (map_zsmul (LinearMap.lTensorHom A) (n + 1) (g (n + 1))).symm

/-- The sum `T_A ⊗ 1 + 1 ⊗ T_B`. -/
noncomputable def tensorTranslation (TA : End ℂ A) (TB : End ℂ B) :
    End ℂ (A ⊗[ℂ] B) :=
  LinearMap.rTensor B TA + LinearMap.lTensor A TB

theorem dcovariant_firstField {TA : End ℂ A} {TB : End ℂ B}
    {f : FormalDist (End ℂ A)} (hf : Reconstruction.DCovariant TA f) :
    Reconstruction.DCovariant (tensorTranslation TA TB) (firstField f) := by
  intro n
  have hcross : LinearMap.lTensor A TB * LinearMap.rTensor B (f n)
      = LinearMap.rTensor B (f n) * LinearMap.lTensor A TB := by
    simpa only [Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [tensorTranslation, firstField, firstField, add_mul, mul_add]
  calc
    (LinearMap.rTensor B TA * LinearMap.rTensor B (f n)
          + LinearMap.lTensor A TB * LinearMap.rTensor B (f n))
        - (LinearMap.rTensor B (f n) * LinearMap.rTensor B TA
          + LinearMap.rTensor B (f n) * LinearMap.lTensor A TB)
      = LinearMap.rTensor B TA * LinearMap.rTensor B (f n)
          - LinearMap.rTensor B (f n) * LinearMap.rTensor B TA := by rw [hcross]; abel
    _ = LinearMap.rTensor B (TA * f n - f n * TA) := by
      rw [← first_mul, ← first_mul, ← LinearMap.rTensor_sub]
    _ = LinearMap.rTensor B ((n + 1) • f (n + 1)) := by rw [hf n]
    _ = (n + 1) • LinearMap.rTensor B (f (n + 1)) := by
      exact map_zsmul (LinearMap.rTensorHom B) (n + 1) (f (n + 1))

theorem dcovariant_secondField {TA : End ℂ A} {TB : End ℂ B}
    {g : FormalDist (End ℂ B)} (hg : Reconstruction.DCovariant TB g) :
    Reconstruction.DCovariant (tensorTranslation TA TB) (secondField g) := by
  intro n
  have hcross : LinearMap.rTensor B TA * LinearMap.lTensor A (g n)
      = LinearMap.lTensor A (g n) * LinearMap.rTensor B TA := by
    simpa only [Module.End.mul_eq_comp, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  rw [tensorTranslation, secondField, secondField, add_mul, mul_add]
  calc
    (LinearMap.rTensor B TA * LinearMap.lTensor A (g n)
          + LinearMap.lTensor A TB * LinearMap.lTensor A (g n))
        - (LinearMap.lTensor A (g n) * LinearMap.rTensor B TA
          + LinearMap.lTensor A (g n) * LinearMap.lTensor A TB)
      = LinearMap.lTensor A TB * LinearMap.lTensor A (g n)
          - LinearMap.lTensor A (g n) * LinearMap.lTensor A TB := by rw [hcross]; abel
    _ = LinearMap.lTensor A (TB * g n - g n * TB) := by
      rw [← second_mul, ← second_mul, ← LinearMap.lTensor_sub]
    _ = LinearMap.lTensor A ((n + 1) • g (n + 1)) := by rw [hg n]
    _ = (n + 1) • LinearMap.lTensor A (g (n + 1)) := by
      exact map_zsmul (LinearMap.lTensorHom A) (n + 1) (g (n + 1))

/-! ## Normal products -/

theorem normalOrdered_firstField (f g : FormalDist (End ℂ A)) (m n : ℤ) :
    normalOrdered (firstField (B := B) f) (firstField g) m n
      = LinearMap.rTensor B (normalOrdered f g m n) := by
  rw [normalOrdered_apply, normalOrdered_apply]
  split_ifs <;> change LinearMap.rTensor B _ * LinearMap.rTensor B _ = _ <;>
    rw [← first_mul]

theorem normalOrdered_secondField (f g : FormalDist (End ℂ B)) (m n : ℤ) :
    normalOrdered (secondField (A := A) f) (secondField g) m n
      = LinearMap.lTensor A (normalOrdered f g m n) := by
  rw [normalOrdered_apply, normalOrdered_apply]
  split_ifs <;> change LinearMap.lTensor A _ * LinearMap.lTensor A _ = _ <;>
    rw [← second_mul]

theorem normalOrdered_firstField_secondField (f : FormalDist (End ℂ A))
    (g : FormalDist (End ℂ B)) (m n : ℤ) :
    normalOrdered (firstField f) (secondField g) m n
      = firstField f m * secondField g n := by
  rw [normalOrdered_apply]
  split_ifs
  · rfl
  · exact (firstField_mul_secondField f g m n).symm

theorem nprod_firstField {f g : FormalDist (End ℂ A)} (hf : IsField f) (hg : IsField g) :
    nprod (isField_firstField (B := B) hf) (isField_firstField hg)
      = firstField (nprod hf hg) := by
  funext s
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]
  | tmul a b =>
      rw [nprod_apply]
      change _ = LinearMap.rTensor B (nprod hf hg s) (a ⊗ₜ[ℂ] b)
      rw [LinearMap.rTensor_tmul, nprod_apply]
      have hfin : (Function.support
          (fun m : ℤ => normalOrdered f g m (s - m) a)).Finite :=
        normalOrdered_diag_support_finite hf hg s a
      rw [finsum_congr (fun m => by
        rw [show normalOrdered (firstField f) (firstField g) m (s - m) (a ⊗ₜ[ℂ] b)
            = LinearMap.rTensor B (normalOrdered f g m (s - m)) (a ⊗ₜ[ℂ] b) from by
              rw [normalOrdered_firstField],
          LinearMap.rTensor_tmul,
          show normalOrdered f g m (s - m) a ⊗ₜ[ℂ] b
            = ((TensorProduct.mk ℂ A B).flip b) (normalOrdered f g m (s - m) a) from rfl])]
      rw [← map_finsum ((TensorProduct.mk ℂ A B).flip b) hfin]
      rfl

theorem nprod_secondField {f g : FormalDist (End ℂ B)} (hf : IsField f) (hg : IsField g) :
    nprod (isField_secondField (A := A) hf) (isField_secondField hg)
      = secondField (nprod hf hg) := by
  funext s
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]
  | tmul a b =>
      rw [nprod_apply]
      change _ = LinearMap.lTensor A (nprod hf hg s) (a ⊗ₜ[ℂ] b)
      rw [LinearMap.lTensor_tmul, nprod_apply]
      have hfin : (Function.support
          (fun m : ℤ => normalOrdered f g m (s - m) b)).Finite :=
        normalOrdered_diag_support_finite hf hg s b
      rw [finsum_congr (fun m => by
        rw [show normalOrdered (secondField f) (secondField g) m (s - m) (a ⊗ₜ[ℂ] b)
            = LinearMap.lTensor A (normalOrdered f g m (s - m)) (a ⊗ₜ[ℂ] b) from by
              rw [normalOrdered_secondField],
          LinearMap.lTensor_tmul,
          show a ⊗ₜ[ℂ] normalOrdered f g m (s - m) b
            = (TensorProduct.mk ℂ A B a) (normalOrdered f g m (s - m) b) from rfl])]
      rw [← map_finsum (TensorProduct.mk ℂ A B a) hfin]
      rfl

/-- The normal product of fields on different factors is their ordinary convolution. -/
theorem nprod_firstField_secondField_apply {f : FormalDist (End ℂ A)}
    {g : FormalDist (End ℂ B)} (hf : IsField f) (hg : IsField g) (s : ℤ)
    (x : A ⊗[ℂ] B) :
    nprod (isField_firstField (B := B) hf) (isField_secondField (A := A) hg) s x
      = ∑ᶠ m : ℤ,
          (firstField (B := B) f m * secondField (A := A) g (s - m)) x := by
  rw [nprod_apply]
  exact finsum_congr fun m => congrArg (· x)
    (normalOrdered_firstField_secondField f g m (s - m))

end
end TensorFieldLift
end VOA
