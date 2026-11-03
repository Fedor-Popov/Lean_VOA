/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzNilDefect
import Mathlib.RingTheory.Nilpotent.Exp

/-! # Actual finite exponential factorization of the three-slot defect -/
namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : Module ℚ X :=
  Module.restrictScalars ℚ ℂ X
local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : IsScalarTower ℚ ℂ X :=
  IsScalarTower.restrictScalars ℚ ℂ X

/-- Actual postcomposition of a bilinear map by an endomorphism. -/
def bilinearPost (E : End ℂ M₃) : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := F.compr₂ E
  map_add' F G := by ext x y; simp
  map_smul' s F := by ext x y; simp

/-- Actual precomposition in the first slot. -/
def bilinearFirst (E : End ℂ M₁) : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := LinearMap.comp F E
  map_add' F G := by ext x y; rfl
  map_smul' s F := by ext x y; rfl

/-- Actual precomposition in the second slot. -/
def bilinearSecond (E : End ℂ M₂) : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := F.compl₂ E
  map_add' F G := by ext x y; rfl
  map_smul' s F := by ext x y; rfl

@[simp] theorem bilinearPost_apply (E : End ℂ M₃) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    bilinearPost E F x y = E (F x y) := rfl
@[simp] theorem bilinearFirst_apply (E : End ℂ M₁) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    bilinearFirst E F x y = F (E x) y := rfl
@[simp] theorem bilinearSecond_apply (E : End ℂ M₂) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    bilinearSecond E F x y = F x (E y) := rfl

@[simp] theorem bilinearPost_pow_apply (E : End ℂ M₃) (j : ℕ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    (bilinearPost E ^ j) F x y = (E ^ j) (F x y) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pow_succ',Module.End.mul_apply,bilinearPost_apply,ih]

@[simp] theorem bilinearFirst_pow_apply (E : End ℂ M₁) (j : ℕ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    (bilinearFirst E ^ j) F x y = F ((E ^ j) x) y := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,bilinearFirst_apply,ih]
    rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]

@[simp] theorem bilinearSecond_pow_apply (E : End ℂ M₂) (j : ℕ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    (bilinearSecond E ^ j) F x y = F x ((E ^ j) y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,bilinearSecond_apply,ih]
    rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]

theorem bilinearPost_nilpotent {E : End ℂ M₃} (hE : IsNilpotent E) : IsNilpotent (bilinearPost (M₁ := M₁) (M₂ := M₂) E) := by
  obtain ⟨j,hj⟩ := hE
  refine ⟨j,?_⟩
  ext F x y
  rw [bilinearPost_pow_apply,hj,LinearMap.zero_apply]
  rfl

theorem bilinearFirst_nilpotent {E : End ℂ M₁} (hE : IsNilpotent E) : IsNilpotent (bilinearFirst (M₂ := M₂) (M₃ := M₃) E) := by
  obtain ⟨j,hj⟩ := hE
  refine ⟨j,?_⟩
  ext F x y
  rw [bilinearFirst_pow_apply,hj,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]
  rfl

theorem bilinearSecond_nilpotent {E : End ℂ M₂} (hE : IsNilpotent E) : IsNilpotent (bilinearSecond (M₁ := M₁) (M₃ := M₃) E) := by
  obtain ⟨j,hj⟩ := hE
  refine ⟨j,?_⟩
  ext F x y
  rw [bilinearSecond_pow_apply,hj,LinearMap.zero_apply,map_zero]
  rfl

theorem exp_bilinearPost_apply {E : End ℂ M₃} (hE : IsNilpotent E) (s : ℂ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    IsNilpotent.exp (s • bilinearPost E) F x y = IsNilpotent.exp (s • E) (F x y) := by
  obtain ⟨j,hj⟩ := hE
  have hp : bilinearPost (M₁ := M₁) (M₂ := M₂) E ^ j = 0 := by
    ext F x y
    rw [bilinearPost_pow_apply,hj,LinearMap.zero_apply]
    rfl
  have hs : (s•E)^j=0 := by rw [smul_pow,hj,smul_zero]
  have hsp : (s•bilinearPost (M₁ := M₁) (M₂ := M₂) E)^j=0 := by rw [smul_pow,hp,smul_zero]
  rw [IsNilpotent.exp_eq_sum hs,IsNilpotent.exp_eq_sum hsp]
  simp only [LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,smul_pow,bilinearPost_pow_apply]

theorem exp_bilinearFirst_apply {E : End ℂ M₁} (hE : IsNilpotent E) (s : ℂ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    IsNilpotent.exp (s • bilinearFirst E) F x y = F (IsNilpotent.exp (s • E) x) y := by
  obtain ⟨j,hj⟩ := hE
  have hp : bilinearFirst (M₂ := M₂) (M₃ := M₃) E ^ j = 0 := by
    ext F x y
    rw [bilinearFirst_pow_apply,hj,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]
    rfl
  have hs : (s•E)^j=0 := by rw [smul_pow,hj,smul_zero]
  have hsp : (s•bilinearFirst (M₂ := M₂) (M₃ := M₃) E)^j=0 := by rw [smul_pow,hp,smul_zero]
  rw [IsNilpotent.exp_eq_sum hs,IsNilpotent.exp_eq_sum hsp]
  simp only [LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,smul_pow,bilinearFirst_pow_apply,
    map_sum,map_rat_smul,map_smul]

theorem exp_bilinearSecond_apply {E : End ℂ M₂} (hE : IsNilpotent E) (s : ℂ)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    IsNilpotent.exp (s • bilinearSecond E) F x y = F x (IsNilpotent.exp (s • E) y) := by
  obtain ⟨j,hj⟩ := hE
  have hp : bilinearSecond (M₁ := M₁) (M₃ := M₃) E ^ j = 0 := by
    ext F x y
    rw [bilinearSecond_pow_apply,hj,LinearMap.zero_apply,map_zero]
    rfl
  have hs : (s•E)^j=0 := by rw [smul_pow,hj,smul_zero]
  have hsp : (s•bilinearSecond (M₁ := M₁) (M₃ := M₃) E)^j=0 := by rw [smul_pow,hp,smul_zero]
  rw [IsNilpotent.exp_eq_sum hs,IsNilpotent.exp_eq_sum hsp]
  simp only [LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,smul_pow,bilinearSecond_pow_apply,
    map_sum,map_rat_smul,map_smul]

/-- The genuine three-slot defect is nilpotent on finite nilpotent input blocks. -/
theorem bilinearDefect_nilpotent {E₁ : End ℂ M₁} {E₂ : End ℂ M₂} {E₃ : End ℂ M₃}
    (h₁ : IsNilpotent E₁) (h₂ : IsNilpotent E₂) (h₃ : IsNilpotent E₃) :
    IsNilpotent (bilinearDefect E₁ E₂ E₃) := by
  let P := bilinearPost (M₁ := M₁) (M₂ := M₂) E₃
  let A := bilinearFirst (M₂ := M₂) (M₃ := M₃) E₁
  let B := bilinearSecond (M₁ := M₁) (M₃ := M₃) E₂
  have hP := bilinearPost_nilpotent (M₁ := M₁) (M₂ := M₂) h₃
  have hA := bilinearFirst_nilpotent (M₂ := M₂) (M₃ := M₃) h₁
  have hB := bilinearSecond_nilpotent (M₁ := M₁) (M₃ := M₃) h₂
  have hPA : Commute P (-A) := by ext F x y; simp [P,A]
  have hPB : Commute P (-B) := by ext F x y; simp [P,B]
  have hAB : Commute (-A) (-B) := by ext F x y; simp [A,B]
  have hD : bilinearDefect E₁ E₂ E₃ = P+(-A)+(-B) := by
    ext F x y
    simp only [LinearMap.add_apply,LinearMap.neg_apply,P,A,B,
      bilinearDefect_apply,bilinearPost_apply,bilinearFirst_apply,bilinearSecond_apply]
    abel
  rw [hD]
  exact (hPB.add_left hAB).isNilpotent_add (hPA.isNilpotent_add hP hA.neg) hB.neg

/-- The three actual commuting nilpotent actions exponentiate by genuine slot transport. -/
theorem exp_bilinearDefect_apply {E₁ : End ℂ M₁} {E₂ : End ℂ M₂} {E₃ : End ℂ M₃}
    (h₁ : IsNilpotent E₁) (h₂ : IsNilpotent E₂) (h₃ : IsNilpotent E₃)
    (s : ℂ) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    IsNilpotent.exp (s • bilinearDefect E₁ E₂ E₃) F x y =
      IsNilpotent.exp (s•E₃) (F (IsNilpotent.exp ((-s)•E₁) x) (IsNilpotent.exp ((-s)•E₂) y)) := by
  let P := bilinearPost (M₁ := M₁) (M₂ := M₂) E₃
  let A := bilinearFirst (M₂ := M₂) (M₃ := M₃) E₁
  let B := bilinearSecond (M₁ := M₁) (M₃ := M₃) E₂
  have hP := bilinearPost_nilpotent (M₁ := M₁) (M₂ := M₂) h₃
  have hA := bilinearFirst_nilpotent (M₂ := M₂) (M₃ := M₃) h₁
  have hB := bilinearSecond_nilpotent (M₁ := M₁) (M₃ := M₃) h₂
  have hPA : Commute (s•P) ((-s)•A) := by ext F x y; simp [P,A]
  have hPB : Commute (s•P) ((-s)•B) := by ext F x y; simp [P,B]
  have hAB : Commute ((-s)•A) ((-s)•B) := by ext F x y; simp [A,B]
  have hD : s•bilinearDefect E₁ E₂ E₃ = s•P+(-s)•A+(-s)•B := by
    ext F x y
    simp only [LinearMap.smul_apply,LinearMap.add_apply,P,A,B,
      bilinearDefect_apply,bilinearPost_apply,bilinearFirst_apply,bilinearSecond_apply]
    module
  rw [hD,IsNilpotent.exp_add_of_commute (hPB.add_left hAB) (hPA.isNilpotent_add (hP.smul s) (hA.smul (-s))) (hB.smul (-s)),
    IsNilpotent.exp_add_of_commute hPA (hP.smul s) (hA.smul (-s))]
  simp only [Module.End.mul_apply]
  rw [exp_bilinearPost_apply h₃,exp_bilinearFirst_apply h₁,exp_bilinearSecond_apply h₂]

end
end VOA.LogTensor.Pz
