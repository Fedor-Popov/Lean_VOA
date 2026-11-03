/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Isomorphisms
import VOA.Core.FiniteAssociatedGraded

/-!
# Kernel flags from ordered evaluation maps

The relative rooted Gordon proof filters a finite functional space by kernels of simultaneous
profile-evaluation maps.  In the intended order a source profile is smaller than every profile
obtained from it by a dominating reassignment or absorption, and the layers are read in descending
order.  This file packages the VOA-free linear algebra of that construction.

For a profile `i`, `laterKernel phi i` is the intersection of the kernels of all later profile
maps.  Its next layer also imposes the kernel of the current map.  The exact layer is canonically
equivalent to the range of the current map restricted to `laterKernel phi i`, and hence injects
into the current profile target.  If one evaluation is injective (the all-singleton evaluation is
the identity in the application), the intersection of all profile kernels is zero.
-/

namespace VOA.GordonKernelFlag

noncomputable section

universe u v w

variable {K : Type u} [DivisionRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type*} [LinearOrder ι]
variable {W : ι → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- Intersection of the kernels of all evaluation maps strictly later than `i`. -/
def laterKernel (phi : ∀ i, V →ₗ[K] W i) (i : ι) : Submodule K V :=
  ⨅ j : {j : ι // i < j}, LinearMap.ker (phi j.1)

/-- The next kernel in the profile flag, obtained by also killing the current evaluation. -/
def currentKernel (phi : ∀ i, V →ₗ[K] W i) (i : ι) : Submodule K V :=
  laterKernel phi i ⊓ LinearMap.ker (phi i)

theorem currentKernel_le_laterKernel (phi : ∀ i, V →ₗ[K] W i) (i : ι) :
    currentKernel phi i ≤ laterKernel phi i :=
  inf_le_left

/-- Every later evaluation vanishes on the later-kernel subspace. -/
theorem laterKernel_le_ker (phi : ∀ i, V →ₗ[K] W i) {i j : ι} (hij : i < j) :
    laterKernel phi i ≤ LinearMap.ker (phi j) := by
  exact iInf_le_of_le (⟨j, hij⟩ : {j : ι // i < j}) le_rfl

/-- The current evaluation restricted to vectors killed by every later evaluation. -/
def restrictedEvaluation (phi : ∀ i, V →ₗ[K] W i) (i : ι) :
    laterKernel phi i →ₗ[K] W i :=
  (phi i).domRestrict (laterKernel phi i)

theorem ker_restrictedEvaluation (phi : ∀ i, V →ₗ[K] W i) (i : ι) :
    LinearMap.ker (restrictedEvaluation phi i) =
      (currentKernel phi i).comap (laterKernel phi i).subtype := by
  ext x
  simp [restrictedEvaluation, currentKernel]

/-- The exact current profile layer is the range of the current evaluation restricted to the
later-kernel subspace. -/
def layerEquivRange (phi : ∀ i, V →ₗ[K] W i) (i : ι) :
    Submodule.Layer (laterKernel phi i) (currentKernel phi i)
        (currentKernel_le_laterKernel phi i) ≃ₗ[K]
      LinearMap.range (restrictedEvaluation phi i) :=
  (Submodule.quotEquivOfEq
      ((currentKernel phi i).comap (laterKernel phi i).subtype)
      (LinearMap.ker (restrictedEvaluation phi i))
      (ker_restrictedEvaluation phi i).symm).trans
    (restrictedEvaluation phi i).quotKerEquivRange

omit [LinearOrder ι] in
/-- If one profile evaluation is injective, the simultaneous kernel of every profile evaluation
is zero.  In the rooted application this is supplied by the all-singleton identity evaluation. -/
theorem iInf_ker_eq_bot_of_injective (phi : ∀ i, V →ₗ[K] W i) (i : ι)
    (hi : Function.Injective (phi i)) :
    (⨅ j : ι, LinearMap.ker (phi j)) = ⊥ := by
  apply le_antisymm
  · calc
      (⨅ j : ι, LinearMap.ker (phi j)) ≤ LinearMap.ker (phi i) := iInf_le _ i
      _ = ⊥ := LinearMap.ker_eq_bot.mpr hi
  · exact bot_le

end

end VOA.GordonKernelFlag
