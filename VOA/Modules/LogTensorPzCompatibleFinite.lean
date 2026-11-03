/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzCompatibleLift
import VOA.Modules.LogTensorFinMain

/-! # Faithful linear compatible-map reconstruction and fusion finiteness -/

namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ R : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup R] [Module ℂ R]
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)

private theorem CompatibleMap.regular
    {psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hpsi : CompatibleMap N₁ N₂ N psi) (r : R) :
    psi r ∈ regularForms N₁.toWeakModule N₂.toWeakModule :=
  fun d u hu => ⟨hpsi.truncated r d u hu,hpsi.compatible r d u hu⟩

/-- The genuine compatible generalized-module maps form a linear subspace. -/
noncomputable def compatibleMaps : Submodule ℂ (R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)) where
  carrier := {psi | CompatibleMap N₁ N₂ N psi}
  zero_mem' := by
    refine ⟨?_,?_,?_⟩
    · intro d u hu p r
      rw [← tauEnd_apply]
      exact (tauEnd N₁.toWeakModule N₂.toWeakModule d u p).map_zero.symm
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).zero_mem d u hu).1
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).zero_mem d u hu).2
  add_mem' hpsi hphi := by
    refine ⟨?_,?_,?_⟩
    · intro d u hu p r
      simp only [LinearMap.add_apply,hpsi.map_mode d u hu p r,hphi.map_mode d u hu p r]
      simp only [← tauEnd_apply,map_add]
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).add_mem
        (hpsi.regular N₁ N₂ N r) (hphi.regular N₁ N₂ N r) d u hu).1
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).add_mem
        (hpsi.regular N₁ N₂ N r) (hphi.regular N₁ N₂ N r) d u hu).2
  smul_mem' s psi hpsi := by
    refine ⟨?_,?_,?_⟩
    · intro d u hu p r
      simp only [LinearMap.smul_apply,hpsi.map_mode d u hu p r]
      simp only [← tauEnd_apply,map_smul]
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).smul_mem s
        (hpsi.regular N₁ N₂ N r) d u hu).1
    · intro r d u hu
      exact ((regularForms N₁.toWeakModule N₂.toWeakModule).smul_mem s
        (hpsi.regular N₁ N₂ N r) d u hu).2

/-- Actual base modes depend linearly on the actual compatible-map matrix coefficients. -/
theorem baseModes_add (psi phi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)) (n : ℂ) :
    baseModes N₁ N₂ N (psi+phi) n = baseModes N₁ N₂ N psi n + baseModes N₁ N₂ N phi n := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [LinearMap.add_apply,LinearMap.add_apply,
    baseModes_homogeneous N₁ N₂ N (psi+phi) n hx hy,
    baseModes_homogeneous N₁ N₂ N psi n hx hy,
    baseModes_homogeneous N₁ N₂ N phi n hx hy]
  have h : baseFunctional N₁ N₂ N (psi+phi) a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩ =
      baseFunctional N₁ N₂ N psi a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩ +
      baseFunctional N₁ N₂ N phi a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩ := by
    ext r
    simp [baseFunctional]
  rw [h,map_add]
  rfl

theorem baseModes_smul (s : ℂ) (psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)) (n : ℂ) :
    baseModes N₁ N₂ N (s • psi) n = s • baseModes N₁ N₂ N psi n := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  rw [LinearMap.smul_apply,LinearMap.smul_apply,
    baseModes_homogeneous N₁ N₂ N (s • psi) n hx hy,
    baseModes_homogeneous N₁ N₂ N psi n hx hy]
  have h : baseFunctional N₁ N₂ N (s • psi) a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩ =
      s • baseFunctional N₁ N₂ N psi a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩ := by
    ext r
    simp [baseFunctional]
  rw [h,map_smul]
  rfl

/-- The reconstructed logarithmic operator, as an actual linear map between genuine
spaces of compatible maps and logarithmic operators. -/
noncomputable def reconstruction : compatibleMaps N₁ N₂ N →ₗ[ℂ]
    LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule (contraLog N).toWeakModule where
  toFun psi := ⟨compatibleLogModes N₁ N₂ N psi.1,
    compatibleLogModes_isLogIntertwining N₁ N₂ N psi.1 psi.2⟩
  map_add' psi phi := by
    apply Subtype.ext
    funext n k
    change (k.factorial:ℂ)⁻¹ • (nilDefect N₁ N₂ (contraLog N)^k)
      (baseModes N₁ N₂ N (psi.1+phi.1) n) = _
    rw [baseModes_add,map_add,smul_add]
    rfl
  map_smul' s psi := by
    apply Subtype.ext
    funext n k
    change (k.factorial:ℂ)⁻¹ • (nilDefect N₁ N₂ (contraLog N)^k)
      (baseModes N₁ N₂ N (s • psi.1) n) = _
    rw [baseModes_smul,map_smul,smul_comm]
    rfl

/-- The compatible-map reconstruction is faithful. Every homogeneous matrix coefficient
is recovered by choosing its unique exponent from the three actual weights. -/
theorem reconstruction_injective : Function.Injective (reconstruction N₁ N₂ N) := by
  intro psi phi h
  have hzero : ∀ n, baseModes N₁ N₂ N psi.1 n = baseModes N₁ N₂ N phi.1 n := by
    intro n
    have hh := congrArg (fun Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule
      (contraLog N).toWeakModule => Y.1 n 0) h
    change compatibleLogModes N₁ N₂ N psi.1 n 0 = compatibleLogModes N₁ N₂ N phi.1 n 0 at hh
    simpa only [compatibleLogModes,logLift_zero] using hh
  apply Subtype.ext
  apply LinearMap.ext
  intro r
  refine LogFin.induction_on N (C := fun r => psi.1 r = phi.1 r) r ?_ (by simp) ?_
  · intro c r hr
    apply bilinear_ext_homogeneous N₁ N₂
    intro a b x y hx hy
    have hh := congrArg (fun F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] C2Rigid.RestrictedDual N.toGW =>
      C2Rigid.dualPairing N.toGW r (F x y)) (hzero (a+b-c-1))
    dsimp only at hh
    rw [pair_baseModes N₁ N₂ N psi.1 (a+b-c-1) hx hy hr,
      pair_baseModes N₁ N₂ N phi.1 (a+b-c-1) hx hy hr] at hh
    have hc : c = a+b-(a+b-c-1)-1 := by ring
    simpa only [if_pos hc] using hh
  · intro r s hr hs
    rw [map_add,map_add,hr,hs]

/-- Fusion finiteness bounds the genuine space of compatible generalized-module maps. -/
theorem finiteDimensional_compatibleMaps_of_c2Cofinite (hC2 : C2Cofinite W)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
    (h₃ : FinGen (contraLog N).toWeakModule) : FiniteDimensional ℂ (compatibleMaps N₁ N₂ N) := by
  haveI := LogFin.logFusionFiniteFact_of_c2Cofinite hC2 M₁ M₂
    (C2Rigid.RestrictedDual N.toGW) N₁ N₂ (contraLog N) h₁ h₂ h₃
  exact FiniteDimensional.of_injective (reconstruction N₁ N₂ N) (reconstruction_injective N₁ N₂ N)

end VOA.LogTensor.Pz
