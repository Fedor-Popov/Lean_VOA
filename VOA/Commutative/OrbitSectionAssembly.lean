/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.Pi

/-!
# Equivariant assembly of an indexed family of component maps

This file isolates the elementary assembly step needed by the rooted-carrier argument.  A group
`H` acts on a source `V`, on a set of coordinate labels `I`, and on one coordinate target `W`.
An indexed family of linear maps is equivariant when translating both its label and its input
translates its output.  Its product map then intertwines the source action with the action on
functions which simultaneously translates values and permutes coordinates.

The kernel of the product map is the intersection of the component kernels, and equivariance
makes that kernel stable under `H`.  No transitivity or orbit-classification hypothesis is used:
the index type may be an entire coarse-profile fiber containing several orbits.

The action on the product is kept as the explicit operation `reindexSmul`.  This avoids replacing
the standard pointwise action on function spaces by a competing global instance.
-/

namespace VOA.OrbitSectionAssembly

noncomputable section

universe u v w x y

variable {R : Type u} [Semiring R]
variable {H : Type v} [Group H]
variable {I : Type w} [MulAction H I]
variable {V : Type x} [AddCommMonoid V] [Module R V] [MulAction H V]
variable {W : Type y} [AddCommMonoid W] [Module R W] [DistribMulAction H W]

/-- The assembled evaluator into independent coordinates indexed by `I`. -/
def assembledEval (eval : I → V →ₗ[R] W) : V →ₗ[R] (I → W) :=
  LinearMap.pi eval

@[simp]
theorem assembledEval_apply (eval : I → V →ₗ[R] W) (v : V) (i : I) :
    assembledEval eval v i = eval i v :=
  rfl

/-- Translate values by `g` and labels contragrediently by `g⁻¹`.  This is the natural action on
the product target for a group which acts on both the labels and the coordinate values. -/
def reindexSmul (g : H) (f : I → W) : I → W :=
  fun i => g • f (g⁻¹ • i)

@[simp]
theorem reindexSmul_apply (g : H) (f : I → W) (i : I) :
    reindexSmul g f i = g • f (g⁻¹ • i) :=
  rfl

@[simp]
theorem reindexSmul_one (f : I → W) : reindexSmul (1 : H) f = f := by
  ext i
  simp [reindexSmul]

theorem reindexSmul_mul (g h : H) (f : I → W) :
    reindexSmul (g * h) f = reindexSmul g (reindexSmul h f) := by
  ext i
  simp [reindexSmul, mul_smul]

/-- Componentwise equivariance of a family of evaluators. -/
def IsEquivariantFamily (eval : I → V →ₗ[R] W) : Prop :=
  ∀ (g : H) (i : I) (v : V), eval (g • i) (g • v) = g • eval i v

/-- An equivariant component family assembles to an equivariant product map. -/
theorem assembledEval_equivariant (eval : I → V →ₗ[R] W)
    (heval : IsEquivariantFamily (H := H) eval) (g : H) (v : V) :
    assembledEval eval (g • v) = reindexSmul g (assembledEval eval v) := by
  ext i
  simpa [reindexSmul] using heval g (g⁻¹ • i) v

/-- The joint kernel is exactly the intersection of the component kernels. -/
theorem ker_assembledEval (eval : I → V →ₗ[R] W) :
    LinearMap.ker (assembledEval eval) = ⨅ i : I, LinearMap.ker (eval i) :=
  LinearMap.ker_pi eval

/-- The joint kernel of an equivariant family is stable under the group action. -/
theorem smul_mem_ker_assembledEval (eval : I → V →ₗ[R] W)
    (heval : IsEquivariantFamily (H := H) eval) (g : H) {v : V}
    (hv : v ∈ LinearMap.ker (assembledEval eval)) :
    g • v ∈ LinearMap.ker (assembledEval eval) := by
  rw [ker_assembledEval, Submodule.mem_iInf] at hv ⊢
  intro i
  rw [LinearMap.mem_ker]
  calc
    eval i (g • v) = g • eval (g⁻¹ • i) v := by
      simpa using heval g (g⁻¹ • i) v
    _ = g • 0 := by rw [LinearMap.mem_ker.mp (hv (g⁻¹ • i))]
    _ = 0 := smul_zero g

/-- For a group action, membership in the joint kernel is unchanged by translation. -/
theorem smul_mem_ker_assembledEval_iff (eval : I → V →ₗ[R] W)
    (heval : IsEquivariantFamily (H := H) eval) (g : H) (v : V) :
    g • v ∈ LinearMap.ker (assembledEval eval) ↔
      v ∈ LinearMap.ker (assembledEval eval) := by
  constructor
  · intro hgv
    have h := smul_mem_ker_assembledEval eval heval g⁻¹ hgv
    simpa using h
  · exact smul_mem_ker_assembledEval eval heval g

end

end VOA.OrbitSectionAssembly
