/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorUniversal

/-! # The genuine logarithmic tensor object represents the intertwiner space

The canonical postcomposition map is surjective by actual universal
factorization and injective by restricted duality and the literal inclusion of
the maximal compatible carrier in the algebraic tensor dual.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.OrbMcRae
open VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
  (N : LogVModule W R)

/-- An arbitrary genuine tensor morphism gives an actual dual map into the maximal
compatible module, using the canonical double-dual inverse of that module. -/
def tensorAdjoint (f : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom N.toWeakModule) :
    (contraLog N).toWeakModule.Hom (tensorDual hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  homComp (doubleDualInverseHom (tensorDual hC2 N₁ N₂ h₁ h₂))
    (transposeLog (tensorModule hC2 N₁ N₂ h₁ h₂) N f)

/-- The genuine pairing characterizes this adjoint, on arbitrary vectors. -/
theorem tensorAdjoint_pair
    (f : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom N.toWeakModule)
    (r : RestrictedDual N.toGW)
    (q : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :
    dualPairing (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
      ((tensorAdjoint hC2 N₁ N₂ h₁ h₂ N f).toLinearMap r) q =
      dualPairing N.toGW (f.toLinearMap q) r := by
  change dualPairing (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
      ((doubleDualInverseHom (tensorDual hC2 N₁ N₂ h₁ h₂)).toLinearMap
        ((transposeLog (tensorModule hC2 N₁ N₂ h₁ h₂) N f).toLinearMap r)) q = _
  rw [doubleDualInverseHom_pair]
  exact transposeLog_pair (tensorModule hC2 N₁ N₂ h₁ h₂) N f q r

/-- The adjoint is literally completed evaluation of the postcomposed genuine
canonical operator, inside the actual algebraic tensor dual. -/
theorem tensorAdjoint_apply
    (f : (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule.Hom N.toWeakModule)
    (r : RestrictedDual N.toGW) :
    ((tensorAdjoint hC2 N₁ N₂ h₁ h₂ N f).toLinearMap r :
      BilinearDual (M₁ := M₁) (M₂ := M₂)) =
      forward N₁ N₂ N (postcompose f (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) r := by
  refine LogFin.induction_on (contraLog N) (C := fun r =>
    ((tensorAdjoint hC2 N₁ N₂ h₁ h₂ N f).toLinearMap r : BilinearDual) =
      forward N₁ N₂ N (postcompose f (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)) r)
    r ?_ ?_ ?_
  · intro c r hr
    have hs : (tensorAdjoint hC2 N₁ N₂ h₁ h₂ N f).toLinearMap r ∈
        (tensorDual hC2 N₁ N₂ h₁ h₂).weight c :=
      gradedHom_of_isGenGraded (contraLog N).toGW (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
        (tensorAdjoint hC2 N₁ N₂ h₁ h₂ N f)
        (contraLog N).weight_le_maxGenEigenspace
        (tensorDual hC2 N₁ N₂ h₁ h₂).weight_le_maxGenEigenspace c r hr
    apply bilinear_ext_homogeneous N₁ N₂
    intro a b x y hx hy
    have hp := tensorAdjoint_pair hC2 N₁ N₂ h₁ h₂ N f r
      ((tensorIntertwiner hC2 N₁ N₂ h₁ h₂).1 (a+b-c-1) 0 x y)
    rw [tensorIntertwiner_logZero,
      pair_baseModes N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
        (tensorInclusion hC2 N₁ N₂ h₁ h₂).1 (a+b-c-1) hx hy hs] at hp
    have hc : c = a+b-(a+b-c-1)-1 := by ring
    simp only [if_pos hc,tensorInclusion_apply] at hp
    rw [forward_homogeneous N₁ N₂ N _ hx hy hr,postcompose_apply,tensorIntertwiner_logZero]
    exact hp
  · dsimp only
    rw [map_zero,map_zero]
    rfl
  · intro r s hr hs
    simp only [map_add,Submodule.coe_add,hr,hs]

/-- The canonical operator induces the actual linear representing map. -/
def tensorPostcompose :
    moduleHomSpace (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule N.toWeakModule →ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N.toWeakModule where
  toFun f := postcompose (homOfSpace f) (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
  map_add' f g := by
    apply Subtype.ext
    funext n k
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  map_smul' s f := by
    apply Subtype.ext
    funext n k
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

/-- The literal compatible inclusion and actual restricted-dual pairing give
uniqueness of the tensor factor. -/
theorem tensorPostcompose_injective :
    Function.Injective (tensorPostcompose hC2 N₁ N₂ h₁ h₂ N) := by
  intro f g h
  have hadj : ∀ r : RestrictedDual N.toGW,
      (tensorAdjoint hC2 N₁ N₂ h₁ h₂ N (homOfSpace f)).toLinearMap r =
      (tensorAdjoint hC2 N₁ N₂ h₁ h₂ N (homOfSpace g)).toLinearMap r := by
    intro r
    apply Subtype.ext
    rw [tensorAdjoint_apply,tensorAdjoint_apply]
    exact congrArg (fun Y => forward N₁ N₂ N Y r) h
  apply Subtype.ext
  apply LinearMap.ext
  intro q
  apply (C2Rigid.iota_injective N.toGW)
  apply restrictedDual_ext_of_pairing (contraLog N).toGW
  intro c r hr
  change dualPairing (contra N.toGW) r (iota N.toGW (f.1 q)) =
    dualPairing (contra N.toGW) r (iota N.toGW (g.1 q))
  rw [C2Rigid.pairing_iota_all,C2Rigid.pairing_iota_all]
  calc
    dualPairing N.toGW (f.1 q) r =
        dualPairing (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
          ((tensorAdjoint hC2 N₁ N₂ h₁ h₂ N (homOfSpace f)).toLinearMap r) q :=
      (tensorAdjoint_pair hC2 N₁ N₂ h₁ h₂ N (homOfSpace f) r q).symm
    _ = dualPairing (tensorDual hC2 N₁ N₂ h₁ h₂).toGW
          ((tensorAdjoint hC2 N₁ N₂ h₁ h₂ N (homOfSpace g)).toLinearMap r) q := by rw [hadj r]
    _ = dualPairing N.toGW (g.1 q) r :=
      tensorAdjoint_pair hC2 N₁ N₂ h₁ h₂ N (homOfSpace g) r q

/-- Every actual logarithmic intertwiner factors through the genuine tensor object. -/
theorem tensorPostcompose_surjective :
    Function.Surjective (tensorPostcompose hC2 N₁ N₂ h₁ h₂ N) := by
  intro Y
  exact ⟨⟨(tensorFactor hC2 N₁ N₂ h₁ h₂ N Y).toLinearMap,
    (tensorFactor hC2 N₁ N₂ h₁ h₂ N Y).map_act⟩,
    tensorFactor_comp_intertwiner hC2 N₁ N₂ h₁ h₂ N Y⟩

/-- The genuine universal property: actual module morphisms from the tensor object
are linearly equivalent to actual logarithmic intertwining operators. -/
def tensorRepresentingEquiv :
    moduleHomSpace (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule N.toWeakModule ≃ₗ[ℂ]
      LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N.toWeakModule :=
  LinearEquiv.ofBijective (tensorPostcompose hC2 N₁ N₂ h₁ h₂ N)
    ⟨tensorPostcompose_injective hC2 N₁ N₂ h₁ h₂ N,
      tensorPostcompose_surjective hC2 N₁ N₂ h₁ h₂ N⟩

end VOA.C2Rigid.LocalInjective
