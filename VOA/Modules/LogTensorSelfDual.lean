/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArBranches
import VOA.Modules.StronglyRational

/-! # Actual self-duality of the tensor unit from the invariant form

A fully invariant nondegenerate form defines the genuine module isomorphism
V to its restricted contragredient. Finite weight spaces supply surjectivity;
the full FHL mode identity supplies the module-map property.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.SelfDual
open Module (End Dual)
open scoped BigOperators
open Pz Contra Ar
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

abbrev unitLog (W : VertexOperatorAlgebra V) := (adjointModule W).toLog

/-- The invariant form is orthogonal on the actual complex adjoint weights. -/
theorem form_orthogonal (B : W.InvariantForm) {a b : ℂ} (hab : a ≠ b)
    {x y : V} (hx : x ∈ (unitLog W).weight a) (hy : y ∈ (unitLog W).weight b) : B.form x y = 0 := by
  have hL := B.L0_adj x y
  have hxa : W.L 0 x = a • x := (adjointModule W).L0_weight a x hx
  have hyb : W.L 0 y = b • y := (adjointModule W).L0_weight b y hy
  rw [hxa,hyb] at hL
  simp only [map_smul,LinearMap.smul_apply] at hL
  have hz : (a-b) • B.form x y = 0 := by rw [sub_smul,hL,sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

/-- The actual finite-dimensional invariant-form weight map. -/
def formPiece (B : W.InvariantForm) (a : ℂ) :
    (unitLog W).weight a →ₗ[ℂ] Dual ℂ ((unitLog W).weight a) :=
  (LinearMap.comp B.form ((unitLog W).weight a).subtype).compl₂ ((unitLog W).weight a).subtype

/-- The actual invariant-form map into the restricted dual. -/
def formMap (B : W.InvariantForm) : V →ₗ[ℂ] C2Rigid.RestrictedDual (unitLog W).toGW :=
  (DFinsupp.mapRange.linearMap (formPiece B)).comp (LogFin.gradEquiv (unitLog W)).symm.toLinearMap

/-- A homogeneous vector is sent to its literal homogeneous form functional. -/
theorem formMap_homogeneous (B : W.InvariantForm) {a : ℂ} {x : V}
    (hx : x ∈ (unitLog W).weight a) :
    formMap B x = DirectSum.lof ℂ ℂ (fun b => Dual ℂ ((unitLog W).weight b)) a
      (formPiece B a ⟨x,hx⟩) := by
  change DFinsupp.mapRange.linearMap (formPiece B) ((LogFin.gradEquiv (unitLog W)).symm x) = _
  rw [LogFin.gradEquiv_symm_of_mem _ hx]
  change DFinsupp.mapRange.linearMap (formPiece B) (DFinsupp.single a ⟨x,hx⟩) = _
  rw [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single]
  rfl

/-- The actual form-induced restricted-dual pairing on every vector. -/
theorem formMap_pair (B : W.InvariantForm) (x y : V) :
    C2Rigid.dualPairing (unitLog W).toGW y (formMap B x) = B.form x y := by
  refine LogFin.induction_on (unitLog W) (C := fun x =>
    C2Rigid.dualPairing (unitLog W).toGW y (formMap B x) = B.form x y) x ?_ ?_ ?_
  · intro a x hx
    rw [formMap_homogeneous B hx]
    refine LogFin.induction_on (unitLog W) (C := fun y =>
      C2Rigid.dualPairing (unitLog W).toGW y
        (DirectSum.lof ℂ ℂ (fun b => Dual ℂ ((unitLog W).weight b)) a (formPiece B a ⟨x,hx⟩)) = B.form x y)
      y ?_ ?_ ?_
    · intro b y hy
      erw [C2Rigid.dualPairing_lof]
      by_cases hab : a = b
      · subst b
        rw [internalProjTo_coe (unitLog W).toGW.isInternal a ⟨y,hy⟩]
        rfl
      · rw [C2Rigid.internalProjTo_eq_zero_of_ne (unitLog W).toGW hy hab,map_zero,
          form_orthogonal B hab hx hy]
    · dsimp only
      change C2Rigid.dualPairingFlip (unitLog W).toGW
        (DirectSum.lof ℂ ℂ (fun b => Dual ℂ ((unitLog W).weight b)) a (formPiece B a ⟨x,hx⟩)) 0 = B.form x 0
      rw [map_zero,map_zero]
    · intro y z hy hz
      dsimp only at hy hz ⊢
      rw [C2Rigid.dualPairing_add_left,map_add,hy,hz]
  · dsimp only
    rw [map_zero,map_zero,map_zero,LinearMap.zero_apply]
  · intro x z hx hz
    dsimp only at hx hz ⊢
    rw [map_add,map_add,map_add,LinearMap.add_apply,hx,hz]

/-- Left nondegeneracy makes the actual form map injective. -/
theorem formMap_injective (B : W.InvariantForm) (hB : B.leftRadical = ⊥) : Function.Injective (formMap B) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro x hx
  have hzero : B.form x = 0 := by
    ext y
    rw [← formMap_pair B x y,hx,map_zero]
    rfl
  have hm : x ∈ B.leftRadical := hzero
  rw [hB,Submodule.mem_bot] at hm
  exact hm

/-- Every actual weight form map is injective under left nondegeneracy. -/
theorem formPiece_injective (B : W.InvariantForm) (hB : B.leftRadical = ⊥) (a : ℂ) :
    Function.Injective (formPiece B a) := by
  intro x z h
  apply Subtype.ext
  apply formMap_injective B hB
  rw [formMap_homogeneous B x.2,formMap_homogeneous B z.2,h]

/-- Finite adjoint weights make the nondegenerate weight pairing an equivalence. -/
def formPieceEquiv (B : W.InvariantForm) (hB : B.leftRadical = ⊥) (a : ℂ) :
    (unitLog W).weight a ≃ₗ[ℂ] Dual ℂ ((unitLog W).weight a) := by
  letI := (unitLog W).finrank a
  exact LinearEquiv.ofBijective (formPiece B a) ⟨formPiece_injective B hB a,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq.symm)).mp (formPiece_injective B hB a)⟩

/-- The genuine restricted-dual linear equivalence defined by the invariant form. -/
def formEquiv (B : W.InvariantForm) (hB : B.leftRadical = ⊥) :
    V ≃ₗ[ℂ] C2Rigid.RestrictedDual (unitLog W).toGW :=
  (LogFin.gradEquiv (unitLog W)).symm.trans (DFinsupp.mapRange.linearEquiv (formPieceEquiv B hB))

theorem formEquiv_apply (B : W.InvariantForm) (hB : B.leftRadical = ⊥) (x : V) :
    formEquiv B hB x = formMap B x := rfl

/-- Full FHL invariance intertwines the actual module modes on homogeneous states. -/
theorem formMap_mode_homogeneous (B : W.InvariantForm) (hB : B.IsFullyInvariant)
    {d : ℤ} {u : V} (hu : u ∈ W.grading d) (p : ℤ) (x : V) :
    formMap B (mode ((unitLog W).YM u) p x) =
      mode ((contraLog (unitLog W)).YM u) p (formMap B x) := by
  apply C2Rigid.restrictedDual_ext_of_pairing (unitLog W).toGW
  intro a y hy
  rw [formMap_pair,pair_contra_opposite (unitLog W) hu p,formMap_pair,
    oppB_homog (unitLog W).toWeakModule hu p]
  change B.form (W.smul u p x) y = _
  simp only [LinearMap.smul_apply,LinearMap.coe_sum,Finset.sum_apply]
  rw [map_smul,map_sum]
  simp only [map_smul]
  exact hB d u hu p x y

/-- Full invariance proves the actual form-induced map is a genuine module map. -/
theorem formMap_mode (B : W.InvariantForm) (hB : B.IsFullyInvariant) (u : V) (p : ℤ) (x : V) :
    formMap B (mode ((unitLog W).YM u) p x) =
      mode ((contraLog (unitLog W)).YM u) p (formMap B x) := by
  have hu : u ∈ ⨆ d, W.grading d := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => formMap B (mode ((unitLog W).YM u) p x) =
      mode ((contraLog (unitLog W)).YM u) p (formMap B x))
    hu (fun d u hu => formMap_mode_homogeneous B hB hu p x) ?_ ?_
  · simp only [map_zero,mode_zero,LinearMap.zero_apply]
  · intro u v hu hv
    simp only [map_add,mode_add,LinearMap.add_apply,hu,hv]

/-- The actual form map as a genuine weak-module homomorphism. -/
def formHom (B : W.InvariantForm) (hB : B.IsFullyInvariant) :
    (unitLog W).toWeakModule.Hom (contraLog (unitLog W)).toWeakModule where
  toLinearMap := formMap B
  map_act := formMap_mode B hB

/-- Its actual inverse is also a genuine module homomorphism. -/
def formInverseHom (B : W.InvariantForm) (hfull : B.IsFullyInvariant) (hB : B.leftRadical = ⊥) :
    (contraLog (unitLog W)).toWeakModule.Hom (unitLog W).toWeakModule where
  toLinearMap := (formEquiv B hB).symm.toLinearMap
  map_act u p t := by
    apply (formEquiv B hB).injective
    change formEquiv B hB ((formEquiv B hB).symm (mode ((contraLog (unitLog W)).YM u) p t)) =
      formEquiv B hB (mode ((unitLog W).YM u) p ((formEquiv B hB).symm t))
    rw [LinearEquiv.apply_symm_apply,formEquiv_apply,formMap_mode B hfull]
    change _ = mode ((contraLog (unitLog W)).YM u) p (formEquiv B hB ((formEquiv B hB).symm t))
    rw [LinearEquiv.apply_symm_apply]

end
end VOA.LogTensor.SelfDual
