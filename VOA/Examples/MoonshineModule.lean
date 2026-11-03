/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Lattice
import VOA.Core.Automorphism

/-!
# The Moonshine module `V♮`  (Gannon §5.2.2, §7.2.1) — pointer file; `V♮` is built in `VOA/Moonshine/`

"The most famous VOA", constructed in 1984 by Frenkel–Lepowsky–Meurman "in a tour de
force". It is the object at the heart of Monstrous Moonshine and the ultimate target
of the whole project.

* **Construction** (Gannon p. 346, §7.2.1): `V♮` is the `ℤ/2`-orbifold of the Leech
  lattice VOA, `V♮ = 𝒱(Λ)^+ ⊕ (𝒱(Λ)^T)^+`, gluing the `+1`-eigenspace of the lift of
  the `-1`-symmetry of `Λ` to the corresponding piece of the unique `-1`-twisted module
  `𝒱(Λ)^T` (`Modularity.Twisted`). Because `Λ` is self-dual, `𝒱(Λ)` is holomorphic and
  so is `V♮`.
* **Central charge** `c = 24`. Grading: `V♮ = V♮₀ ⊕ V♮₁ ⊕ V♮₂ ⊕ ⋯` with
  `V♮₀ = ℂ1` (one-dimensional), `V♮₁ = {0}` (trivial!), and
  `V♮₂ = ℂω ⊕ (Griess algebra)` of dimension `1 + 196883 = 196884`.
* **Automorphism group** `Aut(V♮) = 𝕄`, the **Monster** finite simple group. Each
  `V♮ₙ` is a finite-dimensional `𝕄`-module.
* **Graded dimension** `χ_{V♮}(τ) = J(τ) = q⁻¹ + 196884 q + ⋯` — the normalised
  hauptmodul (the `j`-function minus `744`). This is the Conway–Norton observation
  (0.3.1) that launched Moonshine.  In this library it is proved by a direct character
  computation (`finrank_gradingNat_eq_coeff_JShift`), not via Zhu's theorem.

## Original design sketch (not compiled; the names below do not exist in the library)

```lean
/-- The Moonshine module `V♮` as the `±1`-orbifold of the Leech lattice VOA. -/
noncomputable def moonshineModule : VertexOperatorAlgebra Vnatural := ...

theorem moonshine_centralCharge : moonshineModule.centralCharge = 24 := ...
theorem moonshine_V1_trivial    : moonshineModule.grading 1 = ⊥ := ...
theorem moonshine_griess_dim    : Module.finrank ℂ (moonshineModule.grading 2) = 196884 := ...
theorem moonshine_aut_monster   : Aut moonshineModule ≃* Monster := ...
theorem moonshine_gradedDim     : gradedDim moonshineModule = jInvariantNormalised := ...  -- `= J(τ)`
```

## Dependencies
* `VOA.Examples.Lattice`, `VOA.Core.Automorphism`,
  `VOA.Modularity.Twisted` (orbifold), and most of the library.

## Status
**Constructed in `VOA/Moonshine/`**: `VOA.Moonshine.moonshine` (TopPairs.lean) gives,
unconditionally, a simple `VertexOperatorAlgebra` on `Vnat = V_Λ^+ × (V_Λ^T)^+` with the FLM block
vertex map, central charge `24`, `V♮₁ = 0`, `dim V♮₂ = 196884` and graded dimension `q·J`
(`#print axioms`: `[propext, Classical.choice, Quot.sound]`). `Aut V♮ ≃* 𝕄` is NOT proved.
This file declares **nothing**; the `moonshineModule` sketch above is illustrative only.  The
remaining open items about `V♮` are `Aut V♮ ≃* 𝕄` and anything Monster-related.

## References
* Gannon §5.2.2, §7.2.1; Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the
  Monster* [201]; Borcherds [69] (Monstrous Moonshine); Conway–Norton.
-/

namespace VOA
-- `V♮` is `VOA.Moonshine.moonshine` (VOA/Moonshine/TopPairs.lean).  Open: `Aut V♮ ≃* 𝕄`.
end VOA
