/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Skew
import VOA.Core.WeakAssoc

/-!
# Skew-symmetry (Gannon 5.1.8)

Skew-symmetry `Y(u,z)v = e^{zT}Y(v,-z)u` (Gannon 5.1.8) is proved from first
principles.  The reconstruction cascade reduces it — `sorry`-free — to the single predicate
`WeakAssocLoc W u` (the `b`-uniform operator skew-locality of the candidate field
`skewDist W u`), and `Core.WeakAssoc` *proves* that predicate via the honest two-sided
`ι_z` formal-calculus completion (FLM §8.8–8.10 / Lepowsky–Li Ch. 2–3): the Goddard-vacuum
uniqueness reduction (`goddard_uniqueness_vac`) together with the master `e^{zT}`-expansion
(`smul_Tpow_expand`) and the `vconv`/`negPowJump` δ-jump kill engine, assembled in
`weakAssocLoc`.

No axiom beyond `propext`/`Classical.choice`/`Quot.sound` is used. The theorem
`VOA.pbw : PBWPrinciple` is irrelevant here.

## What this file exposes
* `skew` — `skewDist W u = W.Y u` (Gannon 5.1.8), via `skewDist_eq_Y_of_weakAssoc` fed the
  proven `Core.WeakAssoc.weakAssocLoc`.
* `skew_mode` — the mode formula `u₍ₙ₎v = ∑ⱼ (1/j!)(-1)^{-n-1-j} Tʲ (v₍-n-1-j₎u)`.

## Status
Complete & `sorry`-free / axiom-free.  Skew-symmetry `skew` (Gannon 5.1.8) and the
mode formula `skew_mode` are proved, the input `WeakAssocLoc` being proved in
`Core.WeakAssoc`.  Verified `#print axioms = [propext, Classical.choice, Quot.sound]`; the
library has no project axiom (`VOA.pbw` is a theorem).

## References
* Gannon §5.1.3, eq. (5.1.8); Frenkel–Huang–Lepowsky §8.8–8.10; Lepowsky–Li Ch. 2–3; Kac §4.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Skew-symmetry (Gannon 5.1.8):** the candidate skew field equals the vertex operator,
`skewDist W u = W.Y u`.  `Core.Skew`'s reduction `skewDist_eq_Y_of_weakAssoc` is fed the proven
`Core.WeakAssoc.weakAssocLoc` (no axiom beyond `propext`/`Classical.choice`/`Quot.sound`). -/
theorem skew (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : skewDist W u = W.Y u :=
  skewDist_eq_Y_of_weakAssoc W u (weakAssocLoc W u)

/-- **The skew mode formula (Gannon 5.1.8):**
`u₍ₙ₎v = ∑ⱼ (1/j!)(-1)^{-n-1-j} Tʲ (v₍-n-1-j₎u)`. -/
theorem skew_mode (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℤ) :
    W.smul u n v
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-n - 1 - j) u)) :=
  skew_mode_of_weakAssoc W u v n (weakAssocLoc W u)

end VertexOperatorAlgebra

end VOA
