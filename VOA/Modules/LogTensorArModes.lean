/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzCompatibleLift
import VOA.Modules.LogTensorContraL0Exp
import VOA.Modules.LogTensorPostcompose

/-! # Genuine logarithmic A_r coefficient data

The opposite-coordinate first state is exp(x L(1)) exp((2r+1)πi L(0))
x^{-2L(0)}. Its Jordan part contributes (-2 log x)^l N^l/l!.
Finite L(1) towers and actual generalized weights construct genuine restricted-
dual coefficients. This file does not assume their Jacobi or derivative identity.
-/
noncomputable section
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- A uniform L(1) cutoff on each genuine generalized-weight space. -/
theorem exists_L1_weight_cutoff (N : LogVModule W M₁) (a : ℂ) :
    ∃ K : ℕ, ∀ j : ℕ, K ≤ j → ∀ x ∈ N.weight a, (L1 N.toGW ^ j) x = 0 := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  obtain ⟨K,hK⟩ := exists_nat_gt (a.re-B)
  refine ⟨K,fun j hj x hx => ?_⟩
  have hm := L1_pow_mem_weight N.toGW hx j
  change (L1 N.toGW ^ j) x ∈ N.weight (a-j) at hm
  have hbot : N.weight (a-j) = ⊥ := by
    by_contra h
    have hh := hB (a-j) h
    have hj' : (K:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    simp only [Complex.sub_re,Complex.natCast_re] at hh
    linarith
  rwa [hbot,Submodule.mem_bot] at hm

noncomputable def L1Cutoff (N : LogVModule W M₁) (a : ℂ) : ℕ :=
  (exists_L1_weight_cutoff N a).choose

theorem L1Cutoff_spec (N : LogVModule W M₁) (a : ℂ) :
    ∀ j : ℕ, L1Cutoff N a ≤ j → ∀ x ∈ N.weight a, (L1 N.toGW ^ j) x = 0 :=
  (exists_L1_weight_cutoff N a).choose_spec

/-- The actual odd-half-turn logarithm used by A_r. -/
def phase (r : ℤ) : ℂ := (2*r+1:ℂ)*(Real.pi*Complex.I)

/-- The first-state endomorphism in the genuine j,l coefficient. The full L(0)
exponential includes its nilpotent part. -/
noncomputable def firstTermEnd (N : LogVModule W M₁) (s : ℂ) (j l : ℕ) : End ℂ M₁ :=
  (L1 N.toGW ^ j) * (L0exp N s).toLinearMap * (N.L0nil ^ l)

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- A genuine opposite-coordinate matrix coefficient, linear in all three inputs. -/
noncomputable def matrixTerm (s q : ℂ) (k j l : ℕ) :
    M₁ →ₗ[ℂ] C2Rigid.RestrictedDual N₃.toGW →ₗ[ℂ] Dual ℂ M₂ :=
  LinearMap.mk₂ ℂ (fun x r =>
    { toFun := fun y => C2Rigid.dualPairingFlip N₃.toGW r
        (Y.1 q k (firstTermEnd N₁ s j l x) y)
      map_add' y z := by simp only [map_add,LinearMap.add_apply]
      map_smul' c y := by simp only [map_smul,RingHom.id_apply] })
    (fun x z r => by ext y; dsimp only; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_add,LinearMap.add_apply])
    (fun c x r => by ext y; dsimp only; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_smul,LinearMap.smul_apply,RingHom.id_apply])
    (fun x r t => by
      ext y
      dsimp only
      simp only [LinearMap.coe_mk,AddHom.coe_mk,C2Rigid.dualPairingFlip_apply,map_add,LinearMap.add_apply])
    (fun c x r => by
      ext y
      dsimp only
      simp only [LinearMap.coe_mk,AddHom.coe_mk,C2Rigid.dualPairingFlip_apply,map_smul,LinearMap.smul_apply,RingHom.id_apply])

@[simp] theorem matrixTerm_apply (s q : ℂ) (k j l : ℕ) (x : M₁)
    (r : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    matrixTerm N₁ N₂ N₃ Y s q k j l x r y =
      C2Rigid.dualPairing N₃.toGW (Y.1 q k (firstTermEnd N₁ s j l x) y) r := rfl

/-- The exact logarithmic coefficient from x^{-2L(0)} and inversion of log x. -/
def coefficient (k j l : ℕ) : ℂ :=
  (j.factorial:ℂ)⁻¹ * ((-2:ℂ)^l * (l.factorial:ℂ)⁻¹) * (-1:ℂ)^(k-l)

/-- The finite actual A_r functional before restricting its genuine output weight. -/
noncomputable def functional (r : ℤ) (n : ℂ) (k : ℕ) (a : ℂ) :
    M₁ →ₗ[ℂ] C2Rigid.RestrictedDual N₃.toGW →ₗ[ℂ] Dual ℂ M₂ :=
  ∑ j ∈ Finset.range (L1Cutoff N₁ a), ∑ l ∈ Finset.range (k+1),
    coefficient k j l • matrixTerm N₁ N₂ N₃ Y (phase r) (2*a-j-n-2) (k-l) j l

/-- Actual homogeneous coefficients, placed in the restricted dual of W₂. -/
noncomputable def block (r : ℤ) (n : ℂ) (k : ℕ) (a c : ℂ) :
    N₁.weight a →ₗ[ℂ] (contraLog N₃).weight c →ₗ[ℂ] C2Rigid.RestrictedDual N₂.toGW :=
  let F := ((functional N₁ N₂ N₃ Y r n k a).comp (N₁.weight a).subtype).compl₂
    ((contraLog N₃).weight c).subtype
  let Q : Dual ℂ M₂ →ₗ[ℂ] C2Rigid.RestrictedDual N₂.toGW :=
    (DirectSum.lof ℂ ℂ (fun b => Dual ℂ (N₂.weight b)) (a+c-n-1)).comp
      ((N₂.weight (a+c-n-1)).subtype.dualMap)
  postModes Q (fun _ _ => F) 0 0

/-- The genuine A_r coefficient data on all actual inputs. -/
noncomputable def modes (r : ℤ) : LogModes M₁ (C2Rigid.RestrictedDual N₃.toGW)
    (C2Rigid.RestrictedDual N₂.toGW) :=
  fun n k => fromBlocks N₁ (contraLog N₃) (block N₁ N₂ N₃ Y r n k)

/-- Its defining actual homogeneous coefficient formula. -/
theorem modes_homogeneous (r : ℤ) (n : ℂ) (k : ℕ) {a c : ℂ}
    {x : M₁} {t : C2Rigid.RestrictedDual N₃.toGW}
    (hx : x ∈ N₁.weight a) (ht : t ∈ (contraLog N₃).weight c) :
    modes N₁ N₂ N₃ Y r n k x t =
      DirectSum.lof ℂ ℂ (fun b => Dual ℂ (N₂.weight b)) (a+c-n-1)
        ((functional N₁ N₂ N₃ Y r n k a x t).comp (N₂.weight (a+c-n-1)).subtype) := by
  rw [modes,fromBlocks_homogeneous N₁ (contraLog N₃) _ hx ht]
  rfl

/-- A_r has its genuine generalized output weight, including all logarithmic terms. -/
theorem modes_weight (r : ℤ) (n : ℂ) (k : ℕ) :
    HasModeWeight N₁ (contraLog N₃) (contraLog N₂) n (modes N₁ N₂ N₃ Y r n k) := by
  intro a c x t hx ht
  rw [modes_homogeneous N₁ N₂ N₃ Y r n k hx ht]
  exact ⟨_,rfl⟩

/-- The actual A_r matrix coefficient and vanishing of foreign weight components. -/
theorem pair_modes (r : ℤ) (n : ℂ) (k : ℕ) {a b c : ℂ} {x : M₁} {y : M₂}
    {t : C2Rigid.RestrictedDual N₃.toGW}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (ht : t ∈ (contraLog N₃).weight c) :
    C2Rigid.dualPairing N₂.toGW y (modes N₁ N₂ N₃ Y r n k x t) =
      if b = a+c-n-1 then functional N₁ N₂ N₃ Y r n k a x t y else 0 := by
  rw [modes_homogeneous N₁ N₂ N₃ Y r n k hx ht]
  erw [C2Rigid.dualPairing_lof N₂.toGW y (a+c-n-1)]
  split_ifs with h
  · subst b
    change functional N₁ N₂ N₃ Y r n k a x t
      (internalProjTo N₂.toGW.isInternal (a+c-n-1) y : M₂) = _
    rw [C2Rigid.internalProjTo_coe_mem N₂.toGW hy]
  · rw [C2Rigid.internalProjTo_eq_zero_of_ne N₂.toGW hy (Ne.symm h)]
    simp only [LinearMap.comp_apply,Submodule.coe_zero,map_zero]

end VOA.LogTensor.Ar
