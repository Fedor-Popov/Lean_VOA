/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.DLNBridgeGalois

/-!
# The kernel-only Ng–Schauenburg contract and its DLN bridge

The consumer `DLNBridge.zhuProjectiveCongruence_of_NS` uses only two pieces of
`NgSchauenburg.ProjectiveCongruenceTheorem`: positivity of a level and the containment of
`Γ(level)` in the projective kernel of every modular lift.  Neither the identification of the
level with the FS exponent nor its minimality is used.

`NSProjectiveKernelAll` is exactly that kernel half, with an arbitrary positive level that is
uniform over the modular lifts of a fixed modular category.  It is implied by
`NSProjectiveCongruenceAll` (proved below) and suffices for the bridge (proved below).

This is a TRUE statement (Ng–Schauenburg, CMP 300 (2010), Theorem 6.8).  It is **not proved**
in this file; see `NSCongruenceOrbit` for its reduction to mixed-indicator residuals.
-/

noncomputable section

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA VOA.Classification.COne VOA.Huang.DLN VOA.Huang.NgSchauenburg CongruenceSubgroup
open scoped MatrixGroups

universe u v w

/-- **Kernel half of Ng–Schauenburg Theorem 6.8, for every modular category.**  For each modular
category there is one positive level `N` such that `Γ(N)` acts by scalars in every genuine lift
of the categorical projective `S, T` action. -/
def NSProjectiveKernelAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    ∃ N : ℕ, 0 < N ∧ ∀ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)),
      IsModularRepresentation F M ρ → ProjectiveKernelContainsGamma ρ N

/-- The full Theorem 6.8 contract implies its kernel half. -/
theorem nsProjectiveKernelAll_of_congruenceAll (h : NSProjectiveCongruenceAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hpos, hall⟩ := h C F M
  exact ⟨fsExponent F, hpos, fun ρ hρ => (hall ρ hρ).1⟩

/-- **Projective congruence of Zhu's representation from the kernel half of NS 6.8 and
DLN 3.10.**  Same transport as `zhuProjectiveCongruence_of_NS`. -/
theorem zhuProjectiveCongruence_of_NSKernel (hNS : NSProjectiveKernelAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) : ZhuProjectiveCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD
  obtain ⟨C, _, _, _, _, _, _, _, _, _, _, F, M, e, a, b, hS, hT, hT'⟩ := hB 𝒱 V hV D hD D' hZD
  classical
  let ρ := matrixRepToLinear (reindexRep e D'.rep)
  have hmod : IsModularRepresentation F M ρ := by
    refine ⟨a, b, fun z i => ?_, fun z i => ?_⟩
    · change matrixRepToLinear (reindexRep e D'.rep) ModularGroup.S z i = _
      rw [matrixRepToLinear_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [reindexRep_apply, hS, mul_assoc]
    · change matrixRepToLinear (reindexRep e D'.rep) ModularGroup.T z i = _
      rw [matrixRepToLinear_apply, Finset.sum_eq_single i]
      · rw [reindexRep_apply, hT]
      · intro j _ hji
        rw [reindexRep_apply, hT' i j (Ne.symm hji), zero_mul]
      · simp
  obtain ⟨N, hpos, hall⟩ := hNS C F M
  have hproj := hall ρ hmod
  refine ⟨N, hpos, fun γ hγ => ?_⟩
  obtain ⟨c, hc⟩ := hproj γ ((NSFinish.inPrincipalCongruence_iff _ γ).mpr hγ)
  refine ⟨(c : ℂ), ?_⟩
  have hm := matrix_eq_smul_of_linear (reindexRep e D'.rep) γ c hc
  ext i j
  have := congrFun (congrFun hm (e.symm i)) (e.symm j)
  rw [reindexRep_apply] at this
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp [Matrix.one_apply]

/-- **Both classification inputs from the kernel half of NS 6.8**, DLN 3.10, DLN 2.3
(`MatrixDLNLifting`) and the scaled twist law (`ZhuGaloisTwistInput`). -/
theorem dln_inputs_of_NSKernel_twist (hNS : NSProjectiveKernelAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} := by
  have hC := zhuCongruence_of_projective (zhuProjectiveCongruence_of_NSKernel hNS hB) hlift
  exact ⟨dlnCongruenceInput_of_zhuCongruence hC,
    galoisSymmetryNontrivialInput_of_word hC (zhuGaloisWord_of_twist hC hT)⟩

/-- The same assembly with the Galois-word contract in place of the twist law. -/
theorem dln_inputs_of_NSKernel (hNS : NSProjectiveKernelAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hW : ZhuGaloisWordInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_contracts (zhuProjectiveCongruence_of_NSKernel hNS hB) hlift hW

end VOA.Huang.DLNBridge
