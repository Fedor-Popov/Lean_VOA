/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzBaseJacobi
import VOA.Modules.LogTensorPzNilDefect

/-! # Genuine P(1) L(0) action and logarithmic defect

The conformal coproduct carries the insertion-point derivative in its first
slot. On a family with the genuine weight law, its L(0) defect is exactly the
three-slot nilpotent defect, without a semisimplicity hypothesis.
-/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

/-- The actual conformal coproduct at the insertion point one. -/
theorem rho_conformal_one (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (b : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    rhoL A₁ A₂ W.conformalVector 1 b x y =
      b x (L0 A₂ y) + b (Lm1 A₁ x) y + b (L0 A₁ x) y := by
  rw [rhoL_apply]
  rw [finsum_eq_sum_of_support_subset _ (s := ({0,1}:Finset ℤ)) (by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
    by_contra h
    exact hi (by rw [IsLogIntertwining.cbz_one_eq,if_neg h,zero_mul]))]
  rw [Finset.sum_insert (by norm_num),Finset.sum_singleton,IsLogIntertwining.cbz_one_eq,
    IsLogIntertwining.cbz_one_eq,if_pos (Or.inl rfl),if_pos (Or.inr rfl),one_mul,one_mul]
  ring

/-- On a weight-correct mode the nilpotent defect equals the full L(0) defect. -/
theorem nilDefect_eq_modeDefect (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) {n : ℂ} {F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃}
    (hF : HasModeWeight N₁ N₂ N₃ n F) :
    nilDefect N₁ N₂ N₃ F = modeDefect N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule n F := by
  ext x y
  refine LogFin.induction_on N₁
    (C := fun x => nilDefect N₁ N₂ N₃ F x y =
      modeDefect N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule n F x y) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => nilDefect N₁ N₂ N₃ F x y =
        modeDefect N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule n F x y) y ?_ ?_ ?_
    · intro b y hy
      rw [nilDefect,bilinearDefect_apply,N₃.L0nil_apply_of_mem (hF hx hy),
        N₁.L0nil_apply_of_mem hx,N₂.L0nil_apply_of_mem hy,modeDefect_apply]
      simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
        map_sub,map_smul,LogVModule.L0op,LinearMap.sub_apply]
      module
    · simp
    · intro y z hy hz
      simp only [map_add,hy,hz]
  · simp
  · intro x z hx hz
    simp only [map_add,LinearMap.add_apply,hx,hz]

end VOA.LogTensor.Pz
