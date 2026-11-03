/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArEquiv
import VOA.Modules.LogTensorTwist

/-! # Genuine logarithmic A-transform naturality

Actual weak-module maps preserve the Jordan half-turn and the finite L(1)
tower. The canonical pairings therefore prove contravariant naturality in
both dual slots, including every higher logarithmic coefficient.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ X₁ X₂ X₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
  {W : VertexOperatorAlgebra V}

/-- Actual module maps commute with every power of the genuine L(1) action. -/
theorem hom_L1w_pow (N : LogVModule W M₁) (B : LogVModule W X₁)
    (f : B.toWeakModule.Hom N.toWeakModule) (j : ℕ) (x : X₁) :
    f.toLinearMap ((L1w B.toGW.toWeakModule ^ j) x) =
      (L1w N.toGW.toWeakModule ^ j) (f.toLinearMap x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ',Module.End.mul_apply]
    have hf : ∀ z, f.toLinearMap (L1w B.toGW.toWeakModule z) =
        L1w N.toGW.toWeakModule (f.toLinearMap z) := f.map_act W.conformalVector 2
    rw [hf,ih]

/-- Actual linear transport respects the finite opposite coefficient tower. -/
theorem twI_transport (N : LogVModule W M₁) (B : LogVModule W X₁)
    (f : B.toWeakModule.Hom N.toWeakModule) (g : X₂ →ₗ[ℂ] M₂) (h : M₃ →ₗ[ℂ] X₃)
    (F : IntertwiningModes M₁ M₂ M₃) (G : IntertwiningModes X₁ X₂ X₃)
    (hG : ∀ q x y, G q x y = h (F q (f.toLinearMap x) (g y)))
    (a n : ℂ) (x : X₁) (y : X₂) :
    twI B.toGW G a n x y = h (twI N.toGW F a n (f.toLinearMap x) (g y)) := by
  obtain ⟨J,hJ⟩ := L1w_pow_eventually B.toGW x
  have hJN : ∀ j, J ≤ j → (L1w N.toGW.toWeakModule ^ j) (f.toLinearMap x) = 0 := by
    intro j hj
    rw [← hom_L1w_pow N B f j x,hJ j hj,map_zero]
  rw [twI_apply_eq_sum B.toGW G a n hJ y,twI_apply_eq_sum N.toGW F a n hJN (g y),map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hG,map_smul,hom_L1w_pow]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (B₁ : LogVModule W X₁) (B₂ : LogVModule W X₂) (B₃ : LogVModule W X₃)
variable (f : B₁.toWeakModule.Hom N₁.toWeakModule)
  (g : B₂.toWeakModule.Hom N₂.toWeakModule) (h : N₃.toWeakModule.Hom B₃.toWeakModule)
  (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The Jordan-prepared actual zeroth modes transport through all three module maps. -/
theorem prepared_transport (q : ℂ) (x : X₁) (y : X₂) :
    zeroFamily B₁ B₂ B₃ (prepared B₁ B₂ B₃ (precompose f g (postcompose h Y))) q x y =
      h.toLinearMap (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) q (f.toLinearMap x) (g.toLinearMap y)) := by
  change h.toLinearMap (Y.1 q 0 (f.toLinearMap (nilExp B₁ (phase 0) x)) (g.toLinearMap y)) =
    h.toLinearMap (Y.1 q 0 (nilExp N₁ (phase 0) (f.toLinearMap x)) (g.toLinearMap y))
  rw [hom_nilExp B₁ N₁ f]

/-- The genuine logarithmic A-transform is natural in all three actual module slots. -/
theorem transform_natural :
    transform B₁ B₂ B₃ (precompose f g (postcompose h Y)) =
      postcompose (transposeLog B₂ N₂ g)
        (precompose f (transposeLog N₃ B₃ h) (transform N₁ N₂ N₃ Y)) := by
  apply transform_ext B₁ B₂ B₃
  intro n a x hx t y
  rw [transform_logZero]
  change C2Rigid.dualPairing B₂.toGW y (modes B₁ B₂ B₃ (precompose f g (postcompose h Y)) 0 n 0 x t) =
    C2Rigid.dualPairing B₂.toGW y ((transposeLog B₂ N₂ g).toLinearMap
      ((transform N₁ N₂ N₃ Y).1 n 0 (f.toLinearMap x) ((transposeLog N₃ B₃ h).toLinearMap t)))
  rw [transposeLog_pair,transform_logZero,
    pair_modes_zero B₁ B₂ B₃ (precompose f g (postcompose h Y)) n hx,
    pair_modes_zero N₁ N₂ N₃ Y n (hom_mem_weight B₁ N₁ f hx)]
  rw [twI_transport N₁ B₁ f g.toLinearMap h.toLinearMap
    (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y))
    (zeroFamily B₁ B₂ B₃ (prepared B₁ B₂ B₃ (precompose f g (postcompose h Y))))
    (prepared_transport N₁ N₂ N₃ B₁ B₂ B₃ f g h Y) a n x y]
  exact (transposeLog_pair N₃ B₃ h _ t).symm

end VOA.LogTensor.Ar
