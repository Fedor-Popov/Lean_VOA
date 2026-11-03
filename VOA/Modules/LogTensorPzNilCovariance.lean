/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzNilExponential
import VOA.Modules.LogTensorPzL0
import VOA.Modules.LogTensorSkewEquiv
import VOA.Modules.LogTensorPrecompose

/-! # Genuine Jordan exponential covariance of logarithmic coefficients

Finite actual generalized weight blocks make the three-slot defect nilpotent.
Its genuine exponential factors through all three Jordan exponentials, and
actual logarithmic reconstruction identifies it with the formal logarithm shift.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
open Contra
noncomputable section
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : Module ℚ X :=
  Module.restrictScalars ℚ ℂ X
local instance (X : Type*) [AddCommGroup X] [Module ℂ X] : IsScalarTower ℚ ℂ X :=
  IsScalarTower.restrictScalars ℚ ℂ X

/-- The genuine Jordan operator restricted to one finite generalized weight piece. -/
def weightNil {M : Type u} [AddCommGroup M] [Module ℂ M] (N : LogVModule W M) (a : ℂ) :
    End ℂ (N.weight a) := N.L0nil.restrict (fun x hx => N.L0nil_mem_weight hx)

@[simp] theorem weightNil_pow_coe {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (a : ℂ) (j : ℕ) (x : N.weight a) :
    ((weightNil N a ^ j) x : M) = (N.L0nil ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ',Module.End.mul_apply]
    change N.L0nil ((weightNil N a ^ j) x : M) = N.L0nil ((N.L0nil ^ j) x)
    rw [ih]

theorem weightNil_nilpotent {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (a : ℂ) : IsNilpotent (weightNil N a) := by
  refine ⟨Module.finrank ℂ (N.weight a),?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((weightNil N a ^ Module.finrank ℂ (N.weight a)) x : M) = 0
  rw [weightNil_pow_coe,nilpotent_weight_bound N x.2]

/-- The finite algebraic exponential is the actual Jordan exponential on a weight piece. -/
theorem exp_weightNil_coe {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) (a s : ℂ) (x : N.weight a) :
    (IsNilpotent.exp (s•weightNil N a) x : M) = nilExp N s x := by
  let J := Module.finrank ℂ (N.weight a)
  have hJ : weightNil N a ^ J = 0 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [weightNil_pow_coe,nilpotent_weight_bound N y.2]
    rfl
  have hsJ : (s•weightNil N a)^J=0 := by rw [smul_pow,hJ,smul_zero]
  rw [IsNilpotent.exp_eq_sum hsJ,nilExp_finite N s (nilpotent_weight_bound N x.2)]
  simp only [LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,Submodule.coe_sum,
    SetLike.val_smul,smul_pow,weightNil_pow_coe]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Rat.cast_smul_eq_qsmul ℂ,smul_smul]
  simp only [Rat.cast_inv,Rat.cast_natCast,div_eq_mul_inv,weightNil_pow_coe]
  rw [mul_comm]
  simp only [SetLike.val_smul,weightNil_pow_coe]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- Actual genuine logarithmic modes restricted to their correct finite output weight. -/
def modeWeightBlock (n : ℂ) (k : ℕ) (a b : ℂ) :
    N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] N₃.weight (a+b-n-1) :=
  LinearMap.mk₂ ℂ (fun x y => ⟨Y.1 n k x y,Y.2.mem_weight x.2 y.2 n k⟩)
    (fun x z y => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)
    (fun x y z => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)

@[simp] theorem modeWeightBlock_coe (n : ℂ) (k : ℕ) (a b : ℂ)
    (x : N₁.weight a) (y : N₂.weight b) :
    (modeWeightBlock N₁ N₂ N₃ Y n k a b x y : M₃) = Y.1 n k x y := rfl

/-- Actual Jacobi forces the Jordan defect coefficient recurrence. -/
theorem nilDefect_logCoeff (n : ℂ) (k : ℕ) :
    nilDefect N₁ N₂ N₃ (Y.1 n k) = ((k:ℂ)+1)•Y.1 n (k+1) := by
  rw [nilDefect_eq_modeDefect N₁ N₂ N₃ (fun hx hy => Y.2.mem_weight hx hy n k),
    modeDefect_logCoeff Y.2]

/-- The finite genuine mode blocks obey exactly the same logarithmic recurrence. -/
theorem blockDefect_logCoeff (n : ℂ) (k : ℕ) (a b : ℂ) :
    bilinearDefect (weightNil N₁ a) (weightNil N₂ b) (weightNil N₃ (a+b-n-1))
      (modeWeightBlock N₁ N₂ N₃ Y n k a b) =
      ((k:ℂ)+1)•modeWeightBlock N₁ N₂ N₃ Y n (k+1) a b := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  have h := congrArg (fun F => F (x:M₁) (y:M₂)) (nilDefect_logCoeff N₁ N₂ N₃ Y n k)
  exact h

/-- Every actual finite weight-block coefficient is recovered by powers of the defect. -/
theorem blockDefect_pow_logZero (n : ℂ) (k : ℕ) (a b : ℂ) :
    (bilinearDefect (weightNil N₁ a) (weightNil N₂ b) (weightNil N₃ (a+b-n-1)) ^ k)
      (modeWeightBlock N₁ N₂ N₃ Y n 0 a b) =
      (k.factorial:ℂ)•modeWeightBlock N₁ N₂ N₃ Y n k a b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih,map_smul,blockDefect_logCoeff,smul_smul,Nat.factorial_succ]
    push_cast
    congr 1
    ring

/-- The actual three Jordan exponentials give the genuine formal logarithm shift
on homogeneous inputs, with no finite-generation or semisimplicity premise. -/
theorem nilExp_logShift_homogeneous (s n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) :
    nilExp N₃ s (Y.1 n 0 (nilExp N₁ (-s) x) (nilExp N₂ (-s) y)) =
      logShift s Y.1 n 0 x y := by
  let D := bilinearDefect (weightNil N₁ a) (weightNil N₂ b) (weightNil N₃ (a+b-n-1))
  have hD : IsNilpotent D := bilinearDefect_nilpotent
    (weightNil_nilpotent N₁ a) (weightNil_nilpotent N₂ b) (weightNil_nilpotent N₃ (a+b-n-1))
  obtain ⟨J,hJ⟩ := hD
  have hYJ : ∀ j, J ≤ j → modeWeightBlock N₁ N₂ N₃ Y n j a b = 0 := by
    intro j hj
    have hz : (j.factorial:ℂ) • modeWeightBlock N₁ N₂ N₃ Y n j a b = 0 := by
      rw [← blockDefect_pow_logZero,show D^j=0 from pow_eq_zero_of_le hj hJ,LinearMap.zero_apply]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast Nat.factorial_ne_zero j)
  have hKY : ∀ j, J ≤ j → Y.1 n j x y = 0 := by
    intro j hj
    exact congrArg (fun F => (F ⟨x,hx⟩ ⟨y,hy⟩ : M₃)) (hYJ j hj)
  have hsJ : (s•D)^J=0 := by rw [smul_pow,hJ,smul_zero]
  have he := exp_bilinearDefect_apply
    (weightNil_nilpotent N₁ a) (weightNil_nilpotent N₂ b) (weightNil_nilpotent N₃ (a+b-n-1))
    s (modeWeightBlock N₁ N₂ N₃ Y n 0 a b) ⟨x,hx⟩ ⟨y,hy⟩
  have hcoe := congrArg (fun z : N₃.weight (a+b-n-1) => (z:M₃)) he
  simp only [exp_weightNil_coe,modeWeightBlock_coe] at hcoe
  rw [← hcoe,IsNilpotent.exp_eq_sum hsJ,logShift_eq_sum Y.2.logFinite J hKY]
  simp only [LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,Submodule.coe_sum,
    SetLike.val_smul,smul_pow,blockDefect_pow_logZero]
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (D^j) (modeWeightBlock N₁ N₂ N₃ Y n 0 a b) =
      (j.factorial:ℂ) • modeWeightBlock N₁ N₂ N₃ Y n j a b :=
    blockDefect_pow_logZero N₁ N₂ N₃ Y n j a b
  rw [hb]
  simp only [LinearMap.smul_apply]
  rw [← Rat.cast_smul_eq_qsmul ℂ]
  simp only [Rat.cast_inv,Rat.cast_natCast,SetLike.val_smul,modeWeightBlock_coe]
  change ((j.factorial:ℂ)⁻¹) • (s^j • ((j.factorial:ℂ) • Y.1 n j x y)) = shc s j 0 • Y.1 n j x y
  simp only [Rat.cast_inv,Rat.cast_natCast,smul_smul,shc,Nat.choose_zero_right,
    Nat.cast_one,one_mul,Nat.sub_zero]
  rw [show (j.factorial:ℂ)⁻¹ * (s^j * (j.factorial:ℂ)) = s^j by
    field_simp [Nat.factorial_ne_zero j]]

/-- Genuine Jordan covariance holds on every actual module vector and log branch. -/
theorem nilExp_logShift (s n : ℂ) (x : M₁) (y : M₂) :
    nilExp N₃ s (Y.1 n 0 (nilExp N₁ (-s) x) (nilExp N₂ (-s) y)) =
      logShift s Y.1 n 0 x y := by
  refine LogFin.induction_on N₁ (C := fun x =>
    nilExp N₃ s (Y.1 n 0 (nilExp N₁ (-s) x) (nilExp N₂ (-s) y)) =
      logShift s Y.1 n 0 x y) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on N₂ (C := fun y =>
      nilExp N₃ s (Y.1 n 0 (nilExp N₁ (-s) x) (nilExp N₂ (-s) y)) =
        logShift s Y.1 n 0 x y) y ?_ ?_ ?_
    · intro b y hy
      exact nilExp_logShift_homogeneous N₁ N₂ N₃ Y s n hx hy
    · dsimp only
      simp only [map_zero]
    · intro y z hy hz
      dsimp only at hy hz ⊢
      simp only [map_add,hy,hz]
  · dsimp only
    simp only [map_zero,LinearMap.zero_apply]
  · intro x z hx hz
    dsimp only at hx hz ⊢
    simp only [map_add,LinearMap.add_apply,hx,hz]

/-- The genuine logarithmic operator identity behind Jordan branch covariance. -/
theorem nilExp_logShift_operator (s : ℂ) :
    postcompose (nilExpHom N₃ s)
      (precompose (nilExpHom N₁ (-s)) (nilExpHom N₂ (-s)) Y) =
      (⟨logShift s Y.1,Y.2.isLogIntertwining_logShift s⟩ :
        LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) := by
  apply logZero_injective
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact nilExp_logShift N₁ N₂ N₃ Y s n x y

/-- Every genuine logarithmic coefficient obeys the same Jordan exponential covariance. -/
theorem nilExp_logShift_all (s n : ℂ) (k : ℕ) (x : M₁) (y : M₂) :
    nilExp N₃ s (Y.1 n k (nilExp N₁ (-s) x) (nilExp N₂ (-s) y)) =
      logShift s Y.1 n k x y :=
  congrArg (fun Z => Z.1 n k x y) (nilExp_logShift_operator N₁ N₂ N₃ Y s)

end
end VOA.LogTensor.Pz
