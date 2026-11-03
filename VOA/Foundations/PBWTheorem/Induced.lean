/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.PBWTheorem.LieRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Injectivity of the bottom map of Lie induction

For a Lie subalgebra `p ⊆ g` and a representation `ρ` of `p` on `U`, Lie induction is presented
(as in `VOA.Foundations.AffineLie`, namespace `PBWInduction`) as the quotient of `U(g) ⊗ U` by the
span of the balancing relations `y x ⊗ u - y ⊗ ρ(x) u`, and `bottom : U → Induced` is
`u ↦ [1 ⊗ u]`.

* `bottom_injective_of_embedding`: if `U` embeds `p`-equivariantly into the restriction of some
  representation of `g`, then `bottom` is injective (universal property of induction).
* `bottom_injective`: `bottom` is always injective.  The embedding is the relative PBW
  representation `rep` on `Multiset A →₀ U` (`PBWTheorem.LieRep`), built from a complement of
  `p` (`Submodule.exists_isCompl`), a basis of it (`Basis.ofVectorSpace`), and a well-ordering of
  the basis index (`WellOrderingRel`).

The definitions below are verbatim copies of `PBWInduction.balancingSet/balancing/bottom`
(with `ℂ` generalized to a field `K` and the universes of `g` and `U` decoupled), so the theorem
applies to `PBWInduction.bottom` by definitional unfolding.
-/

namespace VOA.PBWTheorem

open scoped TensorProduct
open Finsupp Module

variable {K : Type*} [Field K]
variable {g : Type*} [LieRing g] [LieAlgebra K g]
variable {U : Type*} [AddCommGroup U] [Module K U]

/-- The generator-level balancing relations `yx ⊗ u - y ⊗ ρ(x)u` (copy of
`PBWInduction.balancingSet`). -/
def balancingSet (p : LieSubalgebra K g) (rho : p →ₗ⁅K⁆ Module.End K U) :
    Set (UniversalEnvelopingAlgebra K g ⊗[K] U) :=
  {t | ∃ (y : UniversalEnvelopingAlgebra K g) (x : p) (u : U),
    t = (y * UniversalEnvelopingAlgebra.ι K (x : g)) ⊗ₜ[K] u - y ⊗ₜ[K] (rho x u)}

/-- The span of the balancing relations (copy of `PBWInduction.balancing`). -/
noncomputable def balancing (p : LieSubalgebra K g) (rho : p →ₗ⁅K⁆ Module.End K U) :
    Submodule K (UniversalEnvelopingAlgebra K g ⊗[K] U) :=
  Submodule.span K (balancingSet p rho)

/-- The bottom map `u ↦ [1 ⊗ u]` (copy of `PBWInduction.bottom`). -/
noncomputable def bottom (p : LieSubalgebra K g) (rho : p →ₗ⁅K⁆ Module.End K U) :
    U →ₗ[K] (UniversalEnvelopingAlgebra K g ⊗[K] U) ⧸ balancing p rho :=
  (balancing p rho).mkQ.comp (TensorProduct.mk K (UniversalEnvelopingAlgebra K g) U 1)

/-- **Universal property.**  A `p`-equivariant embedding of `U` into a `g`-representation forces
the bottom map of the induced module to be injective. -/
theorem bottom_injective_of_embedding (p : LieSubalgebra K g) (rho : p →ₗ⁅K⁆ Module.End K U)
    {M : Type*} [AddCommGroup M] [Module K M] (σ : g →ₗ⁅K⁆ Module.End K M) (j : U →ₗ[K] M)
    (hj : Function.Injective j) (hσ : ∀ (x : p) (u : U), σ (x : g) (j u) = j (rho x u)) :
    Function.Injective (bottom p rho) := by
  let T := UniversalEnvelopingAlgebra.lift K σ
  let B : UniversalEnvelopingAlgebra K g →ₗ[K] U →ₗ[K] M :=
    LinearMap.lcomp K M j ∘ₗ T.toLinearMap
  have hB : ∀ y u, B y u = T y (j u) := fun _ _ => rfl
  let L0 := TensorProduct.lift B
  have hle : balancing p rho ≤ LinearMap.ker L0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, x, u, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L0, TensorProduct.lift.tmul, hB,
      map_mul, Module.End.mul_apply, T, UniversalEnvelopingAlgebra.lift_ι_apply, hσ, sub_self]
  let L := (balancing p rho).liftQ L0 hle
  have hL : ∀ u, L (bottom p rho u) = j u := by
    intro u
    simp only [L, bottom, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      TensorProduct.mk_apply, L0, TensorProduct.lift.tmul, hB, map_one, Module.End.one_apply]
  intro u₁ u₂ h
  apply hj
  rw [← hL u₁, ← hL u₂, h]

/-- **Relative PBW: the bottom of every Lie-induced module embeds.**  For every Lie subalgebra
`p ⊆ g` (any dimension) and every representation `ρ` of `p`, the map `u ↦ [1 ⊗ u]` into
`U(g) ⊗_{U(p)} U` is injective. -/
theorem bottom_injective (p : LieSubalgebra K g) (rho : p →ₗ⁅K⁆ Module.End K U) :
    Function.Injective (bottom p rho) := by
  obtain ⟨c, hc⟩ := Submodule.exists_isCompl p.toSubmodule
  let bc := Basis.ofVectorSpace K c
  letI : LinearOrder (Basis.ofVectorSpaceIndex K c) := WellOrderingRel.isWellOrder.linearOrder
  exact bottom_injective_of_embedding p rho (rep p hc bc rho) (Finsupp.lsingle 0)
    (Finsupp.single_injective 0) (fun x u => rep_p_zero p hc bc rho x u)

end VOA.PBWTheorem
