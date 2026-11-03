/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorMaps
import VOA.Modules.LogTensorSkewNatural

/-! # Actual logarithmic tensor swap isomorphisms

The genuine Ω operator and the proved tensor universal property construct
actual module maps swapping the tensor factors. Ω_{−r−1} supplies their actual
inverse. Hexagon coherence depends subsequently on logarithmic associativity.
-/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

/-- The actual tensor swap map induced by the genuine logarithmic Ω_r. -/
def tensorBraid (r : ℤ) : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom
    (tensorModule hC2 N₂ N₁ h₂ h₁).toWeakModule :=
  tensorFactor hC2 N₁ N₂ h₁ h₂ (tensorModule hC2 N₂ N₁ h₂ h₁)
    (omegaEquiv N₂.toWeakModule N₁.toWeakModule
      (tensorModule hC2 N₂ N₁ h₂ h₁).toWeakModule r
      (tensorIntertwiner hC2 N₂ N₁ h₂ h₁))

/-- Its defining genuine canonical intertwiner identity. -/
theorem tensorBraid_intertwiner (r : ℤ) :
    postcompose (tensorBraid hC2 N₁ N₂ h₁ h₂ r)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      omegaEquiv N₂.toWeakModule N₁.toWeakModule
        (tensorModule hC2 N₂ N₁ h₂ h₁).toWeakModule r
        (tensorIntertwiner hC2 N₂ N₁ h₂ h₁) :=
  tensorFactor_comp_intertwiner hC2 N₁ N₂ h₁ h₂ (tensorModule hC2 N₂ N₁ h₂ h₁) _

/-- Genuine Ω-inversion and universal uniqueness prove the actual inverse law. -/
theorem tensorBraid_inverse_comp (r : ℤ) :
    (homComp (tensorBraid hC2 N₂ N₁ h₂ h₁ (-r-1))
      (tensorBraid hC2 N₁ N₂ h₁ h₂ r)).toLinearMap = LinearMap.id := by
  apply tensor_morphism_ext hC2 N₁ N₂ h₁ h₂ (tensorModule hC2 N₁ N₂ h₁ h₂)
    (g := weakIdentity (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule)
  have hpost : postcompose
      (homComp (tensorBraid hC2 N₂ N₁ h₂ h₁ (-r-1))
        (tensorBraid hC2 N₁ N₂ h₁ h₂ r)) (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) =
      postcompose (tensorBraid hC2 N₂ N₁ h₂ h₁ (-r-1))
        (postcompose (tensorBraid hC2 N₁ N₂ h₁ h₂ r)
          (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl
  rw [hpost,tensorBraid_intertwiner]
  rw [← omega_postcompose (tensorIntertwiner hC2 N₂ N₁ h₂ h₁)
    (tensorBraid hC2 N₂ N₁ h₂ h₁ (-r-1)) r,tensorBraid_intertwiner]
  have hid : postcompose (weakIdentity (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) = tensorIntertwiner hC2 N₁ N₂ h₁ h₂ := by
    apply Subtype.ext
    funext n k
    ext x y
    rfl
  rw [hid]
  apply Subtype.ext
  have h := (tensorIntertwiner hC2 N₁ N₂ h₁ h₂).2.omega_omega (-r-1)
  rw [show -(-r-1)-1 = r by ring] at h
  exact h

/-- The genuine logarithmic tensor swap equivalence. Its two maps are actual
weak-module morphisms, with no new inverse or braiding axiom. -/
def tensorBraidEquiv (r : ℤ) :
    RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW ≃ₗ[ℂ]
      RestrictedDual (tensorDual hC2 N₂ N₁ h₂ h₁).toGW :=
  LinearEquiv.ofLinear (tensorBraid hC2 N₁ N₂ h₁ h₂ r).toLinearMap
    (tensorBraid hC2 N₂ N₁ h₂ h₁ (-r-1)).toLinearMap
    (by
      have h := tensorBraid_inverse_comp hC2 N₂ N₁ h₂ h₁ (-r-1)
      simpa only [show -(-r-1)-1 = r by ring] using h)
    (tensorBraid_inverse_comp hC2 N₁ N₂ h₁ h₂ r)

end VOA.C2Rigid.LocalInjective
