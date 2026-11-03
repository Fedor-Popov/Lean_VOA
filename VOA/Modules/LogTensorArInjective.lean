/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArJacobi
import VOA.Modules.LogTensorPzDoubleDual

/-! # Faithful genuine logarithmic A-transform

The finite L(1) tower has an invertible leading half-turn. Restricted-dual
separation and that triangular tower recover the original zeroth modes.
Genuine logarithmic reconstruction then recovers every coefficient.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Actual restricted duals separate all vectors of a logarithmic module. -/
theorem eq_zero_of_pairing_log (N : LogVModule W M₃) {z : M₃}
    (h : ∀ t : C2Rigid.RestrictedDual N.toGW, C2Rigid.dualPairing N.toGW z t = 0) : z = 0 := by
  apply C2Rigid.iota_injective N.toGW
  apply C2Rigid.restrictedDual_ext_of_pairing (contraLog N).toGW
  intro c t ht
  change C2Rigid.dualPairing (C2Rigid.contra N.toGW) t (C2Rigid.iota N.toGW z) =
    C2Rigid.dualPairing (C2Rigid.contra N.toGW) t (C2Rigid.iota N.toGW 0)
  rw [C2Rigid.pairing_iota_all,C2Rigid.pairing_iota_all,h]
  exact (map_zero (C2Rigid.dualPairingFlip N.toGW t)).symm

/-- The finite actual L(1) tower is faithful on generalized modules. -/
theorem eq_zero_of_twI_log (N : LogVModule W M₁) {F : IntertwiningModes M₁ M₂ M₃}
    (h : ∀ a x, x ∈ N.weight a → ∀ n y, twI N.toGW F a n x y = 0) : F = 0 := by
  have key : ∀ d : ℕ, ∀ a x, x ∈ N.weight a → (L1w N.toGW.toWeakModule ^ d) x = 0 →
      ∀ k y, F k x y = 0 := by
    intro d
    induction d with
    | zero =>
      intro a x _ hx k y
      rw [pow_zero,Module.End.one_apply] at hx
      rw [hx,map_zero,LinearMap.zero_apply]
    | succ d ih =>
      intro a x hx hd k y
      have hJ : ∀ j, d+1 ≤ j → (L1w N.toGW.toWeakModule ^ j) x = 0 :=
        fun j hj => pow_apply_eq_zero_of_le hd hj
      have hhigh : ∀ j : ℕ, ∀ q : ℂ, F q ((L1w N.toGW.toWeakModule ^ (j+1)) x) y = 0 := by
        intro j q
        refine ih (a-(j+1:ℕ)) _ (L1_pow_mem_weight N.toGW hx (j+1)) ?_ q y
        change (L1w N.toGW.toWeakModule ^ d) ((L1w N.toGW.toWeakModule ^ (j+1)) x) = 0
        rw [← Module.End.mul_apply,← pow_add]
        exact pow_apply_eq_zero_of_le hd (by omega)
      have hz := h a x hx (2*a-k-2) y
      rw [twI_apply_eq_sum N.toGW F a _ hJ y,Finset.sum_range_succ'] at hz
      simp only [hhigh,smul_zero,Finset.sum_const_zero,zero_add,Nat.factorial_zero,
        Nat.cast_one,inv_one,one_smul,pow_zero,Module.End.one_apply,CharP.cast_eq_zero,sub_zero] at hz
      rw [show 2*a-(2*a-k-2)-2=k by ring] at hz
      exact (smul_eq_zero.mp hz).resolve_left (statePhase_ne_zero a)
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  refine LogFin.induction_on N (C := fun x => F n x y = 0) x ?_ ?_ ?_
  · intro a x hx
    obtain ⟨J,hJ⟩ := L1w_pow_eventually N.toGW x
    exact key J a x hx (hJ J le_rfl) n y
  · simp only [map_zero,LinearMap.zero_apply]
  · intro x z hx hz
    simp only [map_add,LinearMap.add_apply,hx,hz,add_zero]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

/-- Vanishing of the actual A-transform forces vanishing of the original operator. -/
theorem eq_zero_of_transform
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (h : transform N₁ N₂ N₃ Y = 0) : Y = 0 := by
  have ht : ∀ a x, x ∈ N₁.weight a → ∀ n y,
      twI N₁.toGW (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y)) a n x y = 0 := by
    intro a x hx n y
    apply eq_zero_of_pairing_log N₃
    intro t
    rw [← pair_modes_zero N₁ N₂ N₃ Y n hx]
    rw [← transform_logZero N₁ N₂ N₃ Y n]
    have hz := congrArg (fun Z => Z.1 n 0 x t) h
    change (transform N₁ N₂ N₃ Y).1 n 0 x t = 0 at hz
    rw [hz,map_zero]
  have hf := eq_zero_of_twI_log N₁ ht
  have hp : prepared N₁ N₂ N₃ Y = 0 := by
    apply logZero_injective
    exact hf
  apply Subtype.ext
  funext n k
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hz := congrArg (fun Z => Z.1 n k ((nilExp N₁ (phase 0)).symm x) y) hp
  change Y.1 n k (nilExp N₁ (phase 0) ((nilExp N₁ (phase 0)).symm x)) y = 0 at hz
  rw [LinearEquiv.apply_symm_apply] at hz
  exact hz

/-- Genuine logarithmic operators into a restricted dual are determined by their
zeroth pairings on homogeneous first inputs. -/
theorem transform_ext
    {Y Z : LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule}
    (h : ∀ n a x, x ∈ N₁.weight a → ∀ t y,
      C2Rigid.dualPairing N₂.toGW y (Y.1 n 0 x t) = C2Rigid.dualPairing N₂.toGW y (Z.1 n 0 x t)) : Y = Z := by
  apply logZero_injective
  funext n
  apply bilinear_ext_homogeneous N₁ (contraLog N₃)
  intro a c x t hx ht
  apply C2Rigid.restrictedDual_ext_of_pairing N₂.toGW
  intro b y hy
  exact h n a x hx t y

/-- A genuine A-transform is additive in the intertwiner. -/
theorem transform_add
    (Y Z : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    transform N₁ N₂ N₃ (Y+Z) = transform N₁ N₂ N₃ Y + transform N₁ N₂ N₃ Z := by
  apply transform_ext N₁ N₂ N₃
  intro n a x hx t y
  have hp : zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ (Y+Z)) =
      zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) + zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Z) := rfl
  simp only [Submodule.coe_add,Pi.add_apply,LinearMap.add_apply,map_add]
  rw [transform_logZero,transform_logZero,transform_logZero,
    pair_modes_zero N₁ N₂ N₃ (Y+Z) n hx,pair_modes_zero N₁ N₂ N₃ Y n hx,
    pair_modes_zero N₁ N₂ N₃ Z n hx,hp,twI_add_Y,C2Rigid.dualPairing_add_left]

/-- A genuine A-transform commutes with scalar multiplication. -/
theorem transform_smul (s : ℂ)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    transform N₁ N₂ N₃ (s•Y) = s•transform N₁ N₂ N₃ Y := by
  apply transform_ext N₁ N₂ N₃
  intro n a x hx t y
  have hp : zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ (s•Y)) =
      s•zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) := rfl
  simp only [SetLike.val_smul,Pi.smul_apply,LinearMap.smul_apply,map_smul]
  rw [transform_logZero,transform_logZero,pair_modes_zero N₁ N₂ N₃ (s•Y) n hx,
    pair_modes_zero N₁ N₂ N₃ Y n hx,hp,twI_smul_Y,C2Rigid.dualPairing_smul_left]

/-- The actual logarithmic A-transform as a linear map. -/
noncomputable def transformMap :
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule →ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule where
  toFun := transform N₁ N₂ N₃
  map_add' := transform_add N₁ N₂ N₃
  map_smul' := transform_smul N₁ N₂ N₃

/-- The genuine A-transform loses no logarithmic intertwiner information. -/
theorem transformMap_injective : Function.Injective (transformMap N₁ N₂ N₃) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro Y hY
  exact eq_zero_of_transform N₁ N₂ N₃ Y hY

end VOA.LogTensor.Ar
