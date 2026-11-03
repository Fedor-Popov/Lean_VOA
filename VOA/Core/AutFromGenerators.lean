/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Automorphism
import VOA.Core.BorcherdsIdentity

/-!
# Automorphisms from generators  (infrastructure for Aut(V♮))

A linear equivalence `σ` of a VOA *intertwines* `u` if `σ(u₍ₙ₎y) = (σu)₍ₙ₎(σy)` for all `n, y`.
By the iterate formula (`mode_iterate`, the `m = 0` slice of the Borcherds identity), the set of
intertwined vectors is closed under every product.  It is also a subspace containing `𝟙` when
`σ𝟙 = 𝟙`.  So a linear equivalence fixing `𝟙` and `ω` that intertwines a generating set is
an automorphism.

## Main results
* `Intertwines`, `intertwines_smul` (closure under products), `intertwineSub`.
* `ofGenerators` — the automorphism built from intertwining on a generating set.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace AutGen

/-- `σ` intertwines the modes of `u`. -/
def Intertwines (W : VertexOperatorAlgebra 𝒱) (σ : 𝒱 ≃ₗ[ℂ] 𝒱) (u : 𝒱) : Prop :=
  ∀ (n : ℤ) (y : 𝒱), σ (W.smul u n y) = W.smul (σ u) n (σ y)

/-- A linear equivalence commutes with `finsum`, with or without finite support. -/
theorem linearEquiv_finsum {ι : Type*} (σ : 𝒱 ≃ₗ[ℂ] 𝒱) (f : ι → 𝒱) :
    σ (∑ᶠ i, f i) = ∑ᶠ i, σ (f i) := by
  by_cases hf : (Function.support f).Finite
  · exact map_finsum σ hf
  · have hsupp : Function.support (fun i => σ (f i)) = Function.support f := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff σ σ.injective]
    rw [finsum_of_infinite_support hf, finsum_of_infinite_support (by rwa [hsupp]), map_zero]

variable {W : VertexOperatorAlgebra 𝒱} {σ : 𝒱 ≃ₗ[ℂ] 𝒱}

/-- **Closure under products**: if `σ` intertwines `u` and `v`, it intertwines `u₍ℓ₎v`. -/
theorem intertwines_smul {u v : 𝒱} (hu : Intertwines W σ u) (hv : Intertwines W σ v) (ℓ : ℤ) :
    Intertwines W σ (W.smul u ℓ v) := by
  intro N x
  rw [hu ℓ v, VertexOperatorAlgebra.mode_iterate W u v ℓ N x,
    VertexOperatorAlgebra.mode_iterate W (σ u) (σ v) ℓ N (σ x), linearEquiv_finsum]
  refine finsum_congr fun i => ?_
  rw [map_smul, map_sub, map_smul, hu, hv, hv, hu]

theorem intertwines_zero : Intertwines W σ 0 := by
  intro n y
  rw [PreVertexAlgebra.smul_zero_left, map_zero, PreVertexAlgebra.smul_zero_left]

theorem intertwines_add {u u' : 𝒱} (hu : Intertwines W σ u) (hu' : Intertwines W σ u') :
    Intertwines W σ (u + u') := by
  intro n y
  rw [PreVertexAlgebra.smul_add_left, map_add, hu, hu', map_add, PreVertexAlgebra.smul_add_left]

theorem intertwines_const_smul (c : ℂ) {u : 𝒱} (hu : Intertwines W σ u) :
    Intertwines W σ (c • u) := by
  intro n y
  rw [PreVertexAlgebra.smul_smul_left, map_smul, hu, map_smul, PreVertexAlgebra.smul_smul_left]

theorem intertwines_vacuum (hvac : σ W.vacuum = W.vacuum) : Intertwines W σ W.vacuum := by
  intro n y
  rw [hvac, PreVertexAlgebra.smul_vacuum_left, PreVertexAlgebra.smul_vacuum_left]
  split_ifs <;> simp

variable (W σ) in
/-- The subspace of vectors whose modes `σ` intertwines. -/
def intertwineSub : Submodule ℂ 𝒱 where
  carrier := {u | Intertwines W σ u}
  add_mem' hu hu' := intertwines_add hu hu'
  zero_mem' := intertwines_zero
  smul_mem' c _ hu := intertwines_const_smul c hu

/-- **An automorphism from generators**: a linear equivalence fixing `𝟙` and `ω` and
intertwining the modes of every element of a generating set `G` is a VOA automorphism. -/
def ofGenerators (W : VertexOperatorAlgebra 𝒱) (σ : 𝒱 ≃ₗ[ℂ] 𝒱) (G : Set 𝒱)
    (hgen : ∀ S : Submodule ℂ 𝒱, G ⊆ S → W.vacuum ∈ S →
      (∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, W.smul u n v ∈ S) → S = ⊤)
    (hG : ∀ u ∈ G, Intertwines W σ u) (hvac : σ W.vacuum = W.vacuum)
    (hω : σ W.conformalVector = W.conformalVector) : Aut W where
  toLinearEquiv := σ
  map_smul' u n v := by
    have htop := hgen (intertwineSub W σ) (fun u hu => hG u hu) (intertwines_vacuum hvac)
      (fun u hu v hv n => intertwines_smul hu hv n)
    have hu : u ∈ intertwineSub W σ := htop ▸ Submodule.mem_top
    exact hu n v
  map_vacuum := hvac
  map_omega := hω

@[simp] theorem ofGenerators_apply (W : VertexOperatorAlgebra 𝒱) (σ : 𝒱 ≃ₗ[ℂ] 𝒱) (G : Set 𝒱)
    (hgen) (hG) (hvac) (hω) (v : 𝒱) : ofGenerators W σ G hgen hG hvac hω v = σ v := rfl

end AutGen

end VOA
