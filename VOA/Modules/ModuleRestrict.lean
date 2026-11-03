/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.Twisted

/-!
# Restriction of modules along a sub-VOA

The library has **no module-level reconstruction theorem** — `Core/Reconstruction*.lean` builds
`Y : 𝒱 → End 𝒱` on a *cyclic* space from local fields, and its entire engine (the vacuum-creation
tower, standalone Goddard uniqueness) is unavailable for a module, which has no vacuum and whose
`Y_M` maps *out of* a different space.  So every module in the library so far is either the
adjoint module or a quotient of one.

This file adds the cheapest genuine module-*construction* principle, which needs no reconstruction
machinery at all:

> **A module over a VOA is a module over any sub-VOA**, by restricting the action along the
> inclusion.

Since `𝒱` is a module over itself (`adjointModule`), the immediate corollary is that **`𝒱` is a
module over every sub-VOA of itself** (`VOASubalgebra.adjointRestrict`) — the first modules in the
library that are not the adjoint module of their own algebra.

## Why this matters concretely

For the lattice VOA `V_L` the charge-zero sector is a Heisenberg sub-VOA, and
`gradingLatGen k = ⨆ α, bigradα (k - halfNorm α, α)` already carries the `⟨α,α⟩/2` conformal-weight
shift.  So restriction exhibits `V_L` as a Heisenberg module whose charge-`α` sectors are the
charged Fock modules `F_α` — the B1 objects — with the module Jacobi identity inherited from the
*proved* VOA Jacobi identity rather than re-verified.

## Status

Proved, axiom-clean.  What is deliberately **not** here: the general module reconstruction
theorem (Li's local systems), which would build `Y_M` from generating fields on an arbitrary `M`.
Restriction only produces modules on spaces that already carry a VOA action.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VOASubalgebra

variable {W : VertexOperatorAlgebra 𝒱} (S : VOASubalgebra W)

/-- **Restriction of a weak module along a sub-VOA.**  If `M` is a `W`-module and `S ⊆ W` is a
sub-VOA, then `M` is an `S.toVOA`-module: compose `Y_M` with the inclusion `S ↪ 𝒱`.

Every axiom is the corresponding `W`-axiom evaluated at elements of `S`; nothing is re-proved.
In particular the module Jacobi identity is *inherited*, which is the point — it is the axiom a
module construction otherwise has to establish from scratch. -/
noncomputable def restrictWeakModule {M : Type v} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) : WeakModule S.toVOA M where
  YM := A.YM.comp S.carrier.subtype
  vacuum_YM := A.vacuum_YM
  truncation := fun u x => A.truncation (u : 𝒱) x
  jacobi := fun u v x ℓ m n => A.jacobi (u : 𝒱) (v : 𝒱) x ℓ m n

@[simp] theorem restrictWeakModule_YM {M : Type v} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) (u : S.carrier) :
    (S.restrictWeakModule A).YM u = A.YM (u : 𝒱) := rfl

/-- The mode action is unchanged by restriction. -/
@[simp] theorem restrictWeakModule_act {M : Type v} [AddCommGroup M] [Module ℂ M]
    (A : WeakModule W M) (u : S.carrier) (n : ℤ) (x : M) :
    (S.restrictWeakModule A).act u n x = A.act (u : 𝒱) n x := rfl

/-- **`𝒱` is a module over each of its sub-VOAs.**  Restriction of the adjoint module along the
inclusion: the first modules in the library whose algebra is not their own. -/
noncomputable def adjointRestrict : WeakModule S.toVOA 𝒱 :=
  S.restrictWeakModule (adjointWeakModule W)

@[simp] theorem adjointRestrict_act (u : S.carrier) (n : ℤ) (x : 𝒱) :
    S.adjointRestrict.act u n x = W.smul (u : 𝒱) n x := rfl

end VOASubalgebra

end VOA
