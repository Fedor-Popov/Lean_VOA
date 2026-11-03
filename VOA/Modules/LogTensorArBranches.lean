/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArNatural

/-! # Genuine integer branches of the logarithmic A-transform

Integral conformal turns are actual module automorphisms, including their
nilpotent Jordan part. Inserting such a turn in the first input gives every
FHL A_r branch. The explicit finite coefficient formula respects this branch
transport at every logarithmic degree.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
noncomputable section
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- The actual integer conformal turn exp(2 r pi i L(0)). -/
def branchTurn (N : LogVModule W M₁) (r : ℤ) : M₁ ≃ₗ[ℂ] M₁ :=
  L0exp N ((r:ℂ)*(2*Real.pi*Complex.I))

theorem branchTurn_mode_homogeneous (N : LogVModule W M₁) (r : ℤ)
    {d : ℤ} {u : V} (hu : u ∈ W.grading d) (p : ℤ) (x : M₁) :
    branchTurn N r (mode (N.YM u) p x) = mode (N.YM u) p (branchTurn N r x) := by
  refine LogFin.induction_on N (C := fun x =>
    branchTurn N r (mode (N.YM u) p x) = mode (N.YM u) p (branchTurn N r x)) x ?_ ?_ ?_
  · intro a x hx
    rw [branchTurn,L0exp_apply_of_mem N _ (N.mode_mem_weight hu hx p),
      L0exp_apply_of_mem N _ hx,nilExp_mode,map_smul]
    have he : Complex.exp (((r:ℂ)*(2*Real.pi*Complex.I))*(a+d-p-1)) =
        Complex.exp (((r:ℂ)*(2*Real.pi*Complex.I))*a) := by
      have hc : ((r:ℂ)*(2*Real.pi*Complex.I))*(a+d-p-1) =
          ((r:ℂ)*(2*Real.pi*Complex.I))*a + ((r*(d-p-1):ℤ):ℂ)*(2*Real.pi*Complex.I) := by
        push_cast
        ring
      rw [hc,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
    rw [he]
  · simp only [map_zero]
  · intro x z hx hz
    dsimp only at hx hz ⊢
    simp only [map_add,LinearMap.add_apply,hx,hz]

/-- The actual branch turn commutes with every module mode. -/
theorem branchTurn_mode (N : LogVModule W M₁) (r : ℤ) (u : V) (p : ℤ) (x : M₁) :
    branchTurn N r (mode (N.YM u) p x) = mode (N.YM u) p (branchTurn N r x) := by
  have hu : u ∈ ⨆ d, W.grading d := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => branchTurn N r (mode (N.YM u) p x) = mode (N.YM u) p (branchTurn N r x))
    hu (fun d u hu => branchTurn_mode_homogeneous N r hu p x) ?_ ?_
  · simp only [map_zero,mode_zero,LinearMap.zero_apply]
  · intro u v hu hv
    simp only [map_add,mode_add,LinearMap.add_apply,hu,hv]

/-- Every integer branch turn is a genuine weak-module automorphism. -/
def branchTurnHom (N : LogVModule W M₁) (r : ℤ) : N.toWeakModule.Hom N.toWeakModule where
  toLinearMap := (branchTurn N r).toLinearMap
  map_act := branchTurn_mode N r

private def identityHom (N : WeakModule W M₃) : N.Hom N :=
  ⟨LinearMap.id,fun _ _ _ => rfl⟩

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The actual genuine logarithmic A_r operator, on the prescribed integer branch. -/
def transformBranch (r : ℤ) : LogIntertwiningOperator N₁.toWeakModule
    (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule :=
  precompose (branchTurnHom N₁ r) (identityHom (contraLog N₃).toWeakModule)
    (transform N₁ N₂ N₃ Y)

/-- The first-state finite coefficient operator has the exact full-Jordan branch law. -/
theorem firstTermEnd_branch (N : LogVModule W M₁) (r : ℤ) (j l : ℕ) (x : M₁) :
    firstTermEnd N (phase r) j l x = firstTermEnd N (phase 0) j l (branchTurn N r x) := by
  have hn := hom_L0nil_pow N N (branchTurnHom N r) l x
  change branchTurn N r ((N.L0nil ^ l) x) = (N.L0nil ^ l) (branchTurn N r x) at hn
  change (L1 N.toGW ^ j) (L0exp N (phase r) ((N.L0nil ^ l) x)) =
    (L1 N.toGW ^ j) (L0exp N (phase 0) ((N.L0nil ^ l) (branchTurn N r x)))
  rw [← hn]
  have he : phase 0 + (r:ℂ)*(2*Real.pi*Complex.I) = phase r := by
    unfold phase
    push_cast
    ring
  have hg := DFunLike.congr_fun (L0exp_add N (phase 0) ((r:ℂ)*(2*Real.pi*Complex.I))) ((N.L0nil ^ l) x)
  change L0exp N (phase 0) (branchTurn N r ((N.L0nil ^ l) x)) = _ at hg
  rw [he] at hg
  rw [hg]

/-- The literal FHL finite formula has the branch law at every logarithmic degree. -/
theorem functional_branch (r : ℤ) (n : ℂ) (k : ℕ) (a : ℂ) (x : M₁)
    (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    functional N₁ N₂ N₃ Y r n k a x t y =
      functional N₁ N₂ N₃ Y 0 n k a (branchTurn N₁ r x) t y := by
  simp only [functional,LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [matrixTerm_apply,matrixTerm_apply,firstTermEnd_branch]

/-- The genuine A_r has the exact FHL zeroth logarithmic modes. -/
theorem transformBranch_logZero (r : ℤ) (n : ℂ) :
    (transformBranch N₁ N₂ N₃ Y r).1 n 0 = modes N₁ N₂ N₃ Y r n 0 := by
  apply bilinear_ext_homogeneous N₁ (contraLog N₃)
  intro a c x t hx ht
  apply C2Rigid.restrictedDual_ext_of_pairing N₂.toGW
  intro b y hy
  change C2Rigid.dualPairing N₂.toGW y ((transform N₁ N₂ N₃ Y).1 n 0 (branchTurn N₁ r x) t) = _
  have hbt : branchTurn N₁ r x ∈ N₁.weight a := L0exp_mem_weight N₁ _ hx
  rw [transform_logZero,pair_modes N₁ N₂ N₃ Y 0 n 0
    hbt hy ht,pair_modes N₁ N₂ N₃ Y r n 0 hx hy ht]
  split_ifs with h
  · exact (functional_branch N₁ N₂ N₃ Y r n 0 a x t y).symm
  · rfl

end
end VOA.LogTensor.Ar
