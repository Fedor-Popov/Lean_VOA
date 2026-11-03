/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzL0
import VOA.Modules.LogTensorPzLogLift
import VOA.Modules.LogTensorPzHomogeneous
import VOA.Classification.COne.McRaeM2Graded

/-! # Actual logarithmic intertwiner reconstructed from a compatible generalized map -/

namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ R : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup R] [Module ℂ R]

/-- The genuine contragredient, with its proved generalized eigenspace grading. -/
noncomputable def contraLog (N : LogVModule W R) : LogVModule W (C2Rigid.RestrictedDual N.toGW) :=
  (C2Rigid.contra N.toGW).toLogV
    (C2Rigid.isGenGraded_contra N.toGW (fun a => N.weight_le_maxGenEigenspace a))

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)
variable (psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂))

/-- The reconstructed zeroth modes have the genuine target generalized weight. -/
theorem baseModes_weight (n : ℂ) :
    HasModeWeight N₁ N₂ (contraLog N) n (baseModes N₁ N₂ N psi n) := by
  intro a b x y hx hy
  rw [baseModes_homogeneous N₁ N₂ N psi n hx hy]
  change _ ∈ LinearMap.range
    (DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) (a+b-n-1))
  exact ⟨_,rfl⟩

/-- Compatibility gives the complete genuine Jacobi family on arbitrary inputs. -/
theorem baseModes_isJacobi (hpsi : CompatibleMap N₁ N₂ N psi) :
    IsJacobiFamily N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule
      (baseModes N₁ N₂ N psi) where
  truncation := baseModes_truncated N₁ N₂ N psi
  jacobi := modeJacobi_of_homogeneous N₁ N₂ (contraLog N).toWeakModule
    (baseModes_truncated N₁ N₂ N psi) (fun d u hu a b x y hx hy ell m n =>
      baseModes_jacobi_homogeneous hpsi hu hx hy ell m n)

/-- The compatible conformal coproduct supplies precisely the coupled zeroth
logarithmic derivative equation. -/
theorem baseModes_derivative_modeDefect (hpsi : CompatibleMap N₁ N₂ N psi) (n : ℂ) :
    preLm1 (M₂ := M₂) (M₃ := C2Rigid.RestrictedDual N.toGW) N₁ (baseModes N₁ N₂ N psi n) =
      (-n) • baseModes N₁ N₂ N psi (n-1) +
        modeDefect N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule (n-1)
          (baseModes N₁ N₂ N psi (n-1)) := by
  ext x y
  refine LogFin.induction_on N₁
    (C := fun x => baseModes N₁ N₂ N psi n (Lm1 N₁.toWeakModule x) y =
      ((-n) • baseModes N₁ N₂ N psi (n-1) +
        modeDefect N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule (n-1)
          (baseModes N₁ N₂ N psi (n-1))) x y) x ?_ ?_ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => baseModes N₁ N₂ N psi n (Lm1 N₁.toWeakModule x) y =
        ((-n) • baseModes N₁ N₂ N psi (n-1) +
          modeDefect N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule (n-1)
            (baseModes N₁ N₂ N psi (n-1))) x y) y ?_ ?_ ?_
    · intro b y hy
      apply C2Rigid.restrictedDual_ext_of_pairing N.toGW
      intro c r hr
      have hxm : Lm1 N₁.toWeakModule x ∈ N₁.weight (a+1) := by
        have h := N₁.mode_mem_weight W.conformalVector_mem_grading_two hx 0
        convert h using 2 <;> push_cast <;> ring
      have hx0 : L0 N₁.toWeakModule x ∈ N₁.weight a := N₁.L0op_mem_weight hx
      have hy0 : L0 N₂.toWeakModule y ∈ N₂.weight b := N₂.L0op_mem_weight hy
      simp only [LinearMap.add_apply,LinearMap.smul_apply,modeDefect_apply]
      rw [map_add,map_smul,map_add,map_sub,map_sub,map_smul]
      have hp := pair_mode_baseModes hpsi W.conformalVector_mem_grading_two 1 (n-1) hx hy hr
      change C2Rigid.dualPairing N.toGW r
        (L0 (contraLog N).toWeakModule (baseModes N₁ N₂ N psi (n-1) x y)) = _ at hp
      rw [pair_baseModes N₁ N₂ N psi n hxm hy hr,hp,
        pair_baseModes N₁ N₂ N psi (n-1) hx0 hy hr,
        pair_baseModes N₁ N₂ N psi (n-1) hx hy0 hr,
        pair_baseModes N₁ N₂ N psi (n-1) hx hy hr]
      have he : a+1+b-n-1 = a+b-(n-1)-1 := by ring
      have hc : c-(2:ℤ)+(1:ℤ)+1 = c := by push_cast; ring
      rw [he,hc]
      by_cases h : c = a+b-(n-1)-1
      · simp only [if_pos h,smul_eq_mul]
        rw [rho_conformal_one]
        ring
      · simp only [if_neg h,smul_zero,zero_add,sub_zero]
    · simp
    · intro y z hy hz; simp only [map_add,hy,hz]
  · simp
  · intro x z hx hz; simp only [map_add,LinearMap.add_apply,hx,hz]

/-- The derivative equation uses the actual nilpotent Jordan parts. -/
theorem baseModes_baseDerivative (hpsi : CompatibleMap N₁ N₂ N psi) :
    BaseDerivative N₁ N₂ (contraLog N) (baseModes N₁ N₂ N psi) := by
  intro n
  rw [nilDefect_eq_modeDefect N₁ N₂ (contraLog N) (baseModes_weight N₁ N₂ N psi (n-1))]
  exact baseModes_derivative_modeDefect N₁ N₂ N psi hpsi n

/-- The genuine logarithmic operator reconstructed from the actual compatible map. -/
noncomputable def compatibleLogModes : LogModes M₁ M₂ (C2Rigid.RestrictedDual N.toGW) :=
  logLift N₁ N₂ (contraLog N) (baseModes N₁ N₂ N psi)

/-- The full HLZ compatible-map reconstruction satisfies all four actual logarithmic
intertwiner axioms, without an ordinary-module or rationality hypothesis. -/
theorem compatibleLogModes_isLogIntertwining (hpsi : CompatibleMap N₁ N₂ N psi) :
    IsLogIntertwining N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule
      (compatibleLogModes N₁ N₂ N psi) :=
  isLogIntertwining_logLift N₁ N₂ (contraLog N)
    (baseModes_isJacobi N₁ N₂ N psi hpsi) (baseModes_weight N₁ N₂ N psi)
    (baseModes_baseDerivative N₁ N₂ N psi hpsi)

end VOA.LogTensor.Pz
