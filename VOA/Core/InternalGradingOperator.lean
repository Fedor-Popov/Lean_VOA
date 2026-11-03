/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module

/-!
# The canonical operator of an internal grading

An internal direct-sum grading carries a canonical diagonal operator: prescribe a scalar on each
homogeneous summand and conjugate the resulting operator across the decomposition.  This file
records the construction for an arbitrary index type and proves the basic commutator theorem for
an integer grading.
-/

namespace VOA

open Module (End)

noncomputable section

universe u

variable {A : Type u} [AddCommGroup A] [Module ℂ A]

/-- The diagonal operator attached to an internal grading and a scalar-valued weight function. -/
noncomputable def internalWeightOperator {ι : Type*} [DecidableEq ι]
    (G : ι → Submodule ℂ A)
    (hG : DirectSum.IsInternal G) (weight : ι → ℂ) : End ℂ A := by
  classical
  letI := hG.chooseDecomposition G
  exact (DirectSum.toModule ℂ ι A (fun i => weight i • (G i).subtype)).comp
      (DirectSum.decomposeLinearEquiv G).toLinearMap

/-- Every homogeneous summand is contained in the corresponding eigenspace. -/
theorem grading_le_eigenspace_internalWeightOperator {ι : Type*} [DecidableEq ι]
    (G : ι → Submodule ℂ A) (hG : DirectSum.IsInternal G) (weight : ι → ℂ) (i : ι) :
    G i ≤ Module.End.eigenspace (internalWeightOperator G hG weight) (weight i) := by
  classical
  letI := hG.chooseDecomposition G
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  show (DirectSum.toModule ℂ ι A (fun j => weight j • (G j).subtype))
      ((DirectSum.decomposeLinearEquiv G) x) = weight i • x
  have hdec : (DirectSum.decomposeLinearEquiv G) x =
      DirectSum.of (fun j => (G j : Submodule ℂ A)) i ⟨x, hx⟩ := by
    change DirectSum.decompose G x = _
    exact DirectSum.decompose_coe (ℳ := fun j => (G j : Submodule ℂ A))
      (⟨x, hx⟩ : G i)
  rw [hdec, show (DirectSum.of (fun j => (G j : Submodule ℂ A)) i ⟨x, hx⟩) =
      DirectSum.lof ℂ ι (fun j => (G j : Submodule ℂ A)) i ⟨x, hx⟩ from rfl,
    DirectSum.toModule_lof]
  rfl

/-- A coefficientwise eigenvalue-shift criterion for an internal grading with arbitrary scalar
weights.  Unlike `internalWeightOperatorZ_comm_of_maps`, the target need not be indexed by an
integer grading; this is useful for half-lattice sectors whose eigenvalues are half-integral. -/
theorem internalWeightOperator_comm_of_eigenShift
    {ι : Type*} [DecidableEq ι]
    (G : ι → Submodule ℂ A) (hG : DirectSum.IsInternal G) (weight : ι → ℂ)
    (f : End ℂ A) (d : ℂ)
    (hf : ∀ i x, x ∈ G i →
      internalWeightOperator G hG weight (f x) = (weight i + d) • f x) :
    internalWeightOperator G hG weight * f - f * internalWeightOperator G hG weight =
      d • f := by
  let W := internalWeightOperator G hG weight
  let Z : End ℂ A := W * f - f * W - d • f
  have hpiece : ∀ i, G i ≤ LinearMap.ker Z := by
    intro i x hx
    rw [LinearMap.mem_ker]
    have hxW : W x = weight i • x :=
      Module.End.mem_eigenspace_iff.mp
        (grading_le_eigenspace_internalWeightOperator G hG weight i hx)
    have hfxW : W (f x) = (weight i + d) • f x := hf i x hx
    change (W * f - f * W - d • f) x = 0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hfxW, hxW, map_smul]
    module
  have htop : (⊤ : Submodule ℂ A) ≤ LinearMap.ker Z := by
    rw [← hG.submodule_iSup_eq_top]
    exact iSup_le hpiece
  apply LinearMap.ext
  intro x
  have hxZ : Z x = 0 := LinearMap.mem_ker.mp (htop Submodule.mem_top)
  change (W * f - f * W - d • f) x = 0 at hxZ
  change (W * f - f * W) x = (d • f) x
  exact sub_eq_zero.mp hxZ

/-- The canonical weight operator of an internal integer grading. -/
noncomputable def internalWeightOperatorZ (G : ℤ → Submodule ℂ A)
    (hG : DirectSum.IsInternal G) : End ℂ A :=
  internalWeightOperator G hG (fun n => (n : ℂ))

/-- The integer-graded summand `G n` is an eigenspace of the canonical operator with eigenvalue
`n` (containment is all that is needed below). -/
theorem grading_le_eigenspace_internalWeightOperatorZ (G : ℤ → Submodule ℂ A)
    (hG : DirectSum.IsInternal G) (n : ℤ) :
    G n ≤ Module.End.eigenspace (internalWeightOperatorZ G hG) (n : ℂ) :=
  grading_le_eigenspace_internalWeightOperator G hG (fun m => (m : ℂ)) n

/-- If an endomorphism shifts every homogeneous summand by `d`, its commutator with the canonical
weight operator is exactly `d` times that endomorphism. -/
theorem internalWeightOperatorZ_comm_of_maps
    (G : ℤ → Submodule ℂ A) (hG : DirectSum.IsInternal G)
    (f : End ℂ A) (d : ℤ)
    (hf : ∀ n x, x ∈ G n → f x ∈ G (n + d)) :
    internalWeightOperatorZ G hG * f - f * internalWeightOperatorZ G hG =
      (d : ℂ) • f := by
  let W := internalWeightOperatorZ G hG
  let Z : End ℂ A := W * f - f * W - (d : ℂ) • f
  have hpiece : ∀ n, G n ≤ LinearMap.ker Z := by
    intro n x hx
    rw [LinearMap.mem_ker]
    have hxW : W x = (n : ℂ) • x :=
      Module.End.mem_eigenspace_iff.mp
        (grading_le_eigenspace_internalWeightOperatorZ G hG n hx)
    have hfxW : W (f x) = ((n + d : ℤ) : ℂ) • f x :=
      Module.End.mem_eigenspace_iff.mp
        (grading_le_eigenspace_internalWeightOperatorZ G hG (n + d) (hf n x hx))
    change (W * f - f * W - (d : ℂ) • f) x = 0
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      hfxW, hxW, map_smul]
    push_cast
    module
  have htop : (⊤ : Submodule ℂ A) ≤ LinearMap.ker Z := by
    rw [← hG.submodule_iSup_eq_top]
    exact iSup_le hpiece
  apply LinearMap.ext
  intro x
  have hxZ : Z x = 0 := LinearMap.mem_ker.mp (htop Submodule.mem_top)
  change (W * f - f * W - (d : ℂ) • f) x = 0 at hxZ
  change (W * f - f * W) x = ((d : ℂ) • f) x
  exact sub_eq_zero.mp hxZ

end

end VOA
